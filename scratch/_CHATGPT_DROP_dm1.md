# Q3126 (dm1): R1 — Lean 4 framework design for Ch10 indefinite theta theorems

Date: 2026-07-02

## Executive recommendation

For the first Lean implementation, **do not use `Zsqrtd 5` and do not start with `NumberField.RingOfIntegers`**.  Roll a small custom model of

```text
Z[phi],  phi^2 = phi + 1,
```

as pairs of integers.  This is the best fit for the nine theorems you listed because almost all proofs are elementary polynomial, congruence, and finite-search arguments in the coordinates `(a,b)` of `a+b*phi`.

The central design should be:

```lean
structure PhiInt where
  a : Int
  b : Int
```

with multiplication

```text
(a + b phi) * (c + d phi)
  = (a*c + b*d) + (a*d + b*c + b*d) phi
```

and norm

```text
N(a+b phi) = a^2 + a*b - b^2.
```

Model the coset

```text
L = {a+b phi : b - 3a == 1 mod 10}
```

as a **predicate** or `Set PhiInt`, not as a submodule.  It is an affine coset, not a sublattice.  This is one of the most important Lean design choices.

The recommended staging is:

1. Formalize Tier 1 entirely in a custom coordinate file.  This should be robust and mostly `simp`, `omega`, `ring_nf`, and `nlinarith`.
2. Formalize Tier 2a, the mod-10 unit/coset behavior, in the same coordinate model.
3. Formalize Theorem 9 using explicit finite coefficient lemmas, not by evaluating an infinite q-series.
4. Postpone the full ideal quotient theorem for Theorem 7 until after the algebraic core builds.  In the first pass, prove an explicit CRT-target version `F4 × ZMod 5` and later connect it to `O_K/(2*sqrt5)`.
5. Treat Tier 3 as a coefficient-level bridge theorem before connecting to existing power-series infrastructure.

## 1. Recommended definitions

### 1.1 File header and imports

For the Tier 1 coordinate file, start small:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import QseriesFormalization.Basic

namespace QseriesFormalization
namespace Ch10
```

If `QseriesFormalization.Basic` is not needed for the pure algebra file, omit it there and import it only in the q-series bridge file.  Keeping the algebra file independent will make it faster and less fragile.

### 1.2 `Z[phi]` as pairs

Use a custom type.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization
namespace Ch10

/-- Integer coordinates for `a + b * phi`, where `phi^2 = phi + 1`. -/
structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

instance : Zero PhiInt := ⟨⟨0, 0⟩⟩
instance : One PhiInt := ⟨⟨1, 0⟩⟩
instance : Add PhiInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg PhiInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub PhiInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩

/-- Multiplication in `Z[phi]`, using `phi^2 = phi + 1`. -/
instance : Mul PhiInt :=
  ⟨fun x y =>
    ⟨x.a * y.a + x.b * y.b,
     x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] theorem zero_a : (0 : PhiInt).a = 0 := rfl
@[simp] theorem zero_b : (0 : PhiInt).b = 0 := rfl
@[simp] theorem one_a : (1 : PhiInt).a = 1 := rfl
@[simp] theorem one_b : (1 : PhiInt).b = 0 := rfl
@[simp] theorem add_a (x y : PhiInt) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : PhiInt) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : PhiInt) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : PhiInt) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : PhiInt) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : PhiInt) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : PhiInt) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : PhiInt) :
    (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

/-- `phi = 0 + 1*phi`. -/
def phi : PhiInt := ⟨0, 1⟩

/-- `sqrt 5 = 2*phi - 1`. -/
def sqrt5 : PhiInt := ⟨-1, 2⟩

/-- The totally positive unit `epsilon = phi^2 = 1 + phi`. -/
def eps : PhiInt := ⟨1, 1⟩

/-- Norm from `Z[phi]` to `Z`: `N(a+b phi)=a^2+ab-b^2`. -/
def norm (x : PhiInt) : Int := x.a ^ 2 + x.a * x.b - x.b ^ 2

@[simp] theorem norm_mk (a b : Int) : norm ⟨a, b⟩ = a ^ 2 + a * b - b ^ 2 := rfl

end PhiInt
end Ch10
end QseriesFormalization
```

Do **not** spend time proving a full `CommRing PhiInt` instance in the first pass unless the code starts demanding it.  For Tier 1, the coordinate operations and theorems are enough.  A full ring instance is possible but creates extra proof obligations that do not help the first nine theorems.

### 1.3 Exponent, beta map, coset, and cones

Use integer-valued definitions.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization
namespace Ch10

/-- Twice the exponent. -/
def Q (k r : Int) : Int :=
  4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r

/-- Integer triangular number on `Int`. -/
def triZ (r : Int) : Int := r * (r + 1) / 2

/-- The exponent `E = Q/2`, written without using `Q/2` directly. -/
def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

/-- The atom-to-golden-integer map. -/
def beta (k r : Int) : PhiInt :=
  ⟨r - 2 * k, 4 * k + 3 * r + 1⟩

/-- The affine coset `L = {a+b phi : b - 3a == 1 mod 10}`. -/
def InL (x : PhiInt) : Prop :=
  Int.ModEq 10 (x.b - 3 * x.a) 1

/-- Positive same-sign cone `A`. -/
def InACone (k r : Int) : Prop := 0 <= k ∧ 0 <= r

/-- Negative same-sign cone `D`. -/
def InDCone (k r : Int) : Prop := k < 0 ∧ r < 0

end Ch10
end QseriesFormalization
```

Important note about signs: in Lean, `(-1 : Int) ^ r` is not available for negative integer exponents.  For signs, avoid integer exponents.  Define parity sign by a predicate instead:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace QseriesFormalization
namespace Ch10

/-- The sign `(-1)^n`, defined by parity of an integer. -/
def negOnePowInt (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

@[simp] theorem negOnePowInt_even {n : Int} (h : n % 2 = 0) : negOnePowInt n = 1 := by
  simp [negOnePowInt, h]

@[simp] theorem negOnePowInt_odd {n : Int} (h : n % 2 ≠ 0) : negOnePowInt n = -1 := by
  simp [negOnePowInt, h]

/-- Cone weight for `B = D - A`. -/
def BWeight (k r : Int) : Int :=
  if InACone k r then -negOnePowInt r
  else if InDCone k r then negOnePowInt r
  else 0

end Ch10
end QseriesFormalization
```

This avoids all negative-exponent headaches.

## 2. Coset modeling

Use `InL : PhiInt -> Prop` and optionally a subtype:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace QseriesFormalization
namespace Ch10

abbrev L := {x : PhiInt // InL x}

end Ch10
end QseriesFormalization
```

Do not define `L` as an `AddSubgroup`, because it is not closed under addition.  If you want the underlying index-10 sublattice, define it separately:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace QseriesFormalization
namespace Ch10

def InL0 (x : PhiInt) : Prop :=
  Int.ModEq 10 (x.b - 3 * x.a) 0

end Ch10
end QseriesFormalization
```

For bijection proofs, a `Set.range` theorem is easier than an `Equiv` at first:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace QseriesFormalization
namespace Ch10

/-- The image of `beta` is contained in the affine coset. -/
theorem beta_mem_L (k r : Int) : InL (beta k r) := by
  unfold InL beta
  -- Goal: `10k+1 ≡ 1 [ZMOD 10]`.
  omega

end Ch10
end QseriesFormalization
```

For surjectivity, avoid defining the inverse with `/ 10` if you can.  Use divisibility from `ModEq`.  If the exact `ModEq` lemma names become annoying, define the coset by divisibility from the start:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

def InL_dvd (x : PhiInt) : Prop :=
  10 ∣ x.b - 3 * x.a - 1

/-- The image of `beta` is contained in the divisibility-form affine coset. -/
theorem beta_mem_L_dvd (k r : Int) : InL_dvd (beta k r) := by
  unfold InL_dvd beta
  use k
  ring

/-- Surjectivity of `beta` onto the divisibility-form affine coset. -/
theorem exists_beta_of_mem_L_dvd (x : PhiInt) (hx : InL_dvd x) :
    ∃ k r : Int, beta k r = x := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, x.a + 2 * k, ?_⟩
  ext <;> unfold beta <;> omega

end Ch10
end QseriesFormalization
```

My practical recommendation:

```text
Use divisibility for proofs; expose `Int.ModEq` lemmas for human-facing theorem statements.
```

## 3. File structure

Recommended split:

```text
QseriesFormalization/Ch10/PhiInt.lean
QseriesFormalization/Ch10/ConeAlgebra.lean
QseriesFormalization/Ch10/HMMatch.lean
QseriesFormalization/Ch10/FiniteCounterexample.lean
QseriesFormalization/Ch10/CRTOrder.lean
QseriesFormalization/Ch10/CoefficientFormula.lean
```

### `PhiInt.lean`

Contains:

```text
PhiInt structure
addition/multiplication coordinate operations
phi, sqrt5, eps
norm
basic simp lemmas
optional norm_mul theorem
```

### `ConeAlgebra.lean`

Contains:

```text
Q, triZ, E
beta
InL, InL0
A/D cones
parity sign
Theorems 1--4
Theorem 6 mod-10 instability and eps^6 stability
```

### `HMMatch.lean`

Contains:

```text
HM exponent expression
HM sign simplification
Theorem 8: f_{1,3,4}(X,-X^3,X) exponent matches E(k,r)
```

This can remain pure algebra.  It does not need the actual HM q-series object yet.

### `FiniteCounterexample.lean`

Contains:

```text
manual finite coefficient computations:
B_1 = 1
B_3 = -2
B_34 = 3
nonmultiplicativity on norm values 11 * 31 = 341
```

Do this as a finite/manual theorem first.  Do not depend on full q-series expansion.

### `CRTOrder.lean`

Contains:

```text
explicit F4 × ZMod 5 model
image of eps
order 6 theorem in the CRT target
later: isomorphism with O_K/(2*sqrt5)
```

This file is Tier 2 and can be postponed if it becomes heavy.

### `CoefficientFormula.lean`

Contains Tier 3:

```text
definition of coefficient-level A_N, D_N, B_N
finite support boxes
exact formula as sum over beta in S(N)
bridge to existing q-series infrastructure
```

Keep it last.  It depends on the coefficient infrastructure and will likely be the least stable.

## 4. Proof strategies theorem by theorem

## Theorem 1: `Q(k,r)` is even

Recommended statement:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

theorem Q_even (k r : Int) : 2 ∣ Q k r := by
  unfold Q
  -- Use the decomposition
  -- Q = 2*(2*k^2+k+3*k*r) + r*(r+1)
  -- and prove `2 ∣ r*(r+1)`.
  sorry

end Ch10
end QseriesFormalization
```

No `sorry` in final code, of course.  The proof pattern should be:

1. Prove or import the lemma:

```lean
lemma two_dvd_mul_succ (r : Int) : 2 ∣ r * (r + 1)
```

2. Then combine divisibility:

```lean
have h1 : 2 ∣ 2 * (2*k^2 + k + 3*k*r) := by exact dvd_mul_right 2 _
have h2 : 2 ∣ r * (r + 1) := two_dvd_mul_succ r
have hsum : 2 ∣ 2 * (2*k^2 + k + 3*k*r) + r*(r+1) := dvd_add h1 h2
convert hsum using 1 <;> ring
```

If the imported evenness lemma is hard to find, prove it by parity cases on `r % 2`.  This is a one-time lemma worth having.

## Theorem 2: beta bijection onto `L`

Use two theorems first, not an `Equiv`:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

theorem beta_mem_L_dvd (k r : Int) : InL_dvd (beta k r) := by
  unfold InL_dvd beta
  use k
  ring

theorem exists_beta_of_mem_L_dvd (x : PhiInt) (hx : InL_dvd x) :
    ∃ k r : Int, beta k r = x := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, x.a + 2*k, ?_⟩
  ext <;> unfold beta <;> omega

end Ch10
end QseriesFormalization
```

This is much easier than making an `Equiv` on day one.  Once those build, define the actual equivalence only if another theorem needs it.

## Theorem 3: norm identity

Best statement:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

theorem norm_beta (k r : Int) :
    -PhiInt.norm (beta k r) = 10 * E k r + 1 := by
  unfold PhiInt.norm beta E triZ
  -- Need lemma `2 * (r*(r+1)/2) = r*(r+1)`.
  have htri : 2 * (r * (r + 1) / 2) = r * (r + 1) := by
    -- follows from `2 ∣ r*(r+1)`
    sorry
  nlinarith [htri]

end Ch10
end QseriesFormalization
```

The final code should replace the `sorry` with a lemma:

```lean
lemma two_mul_triZ (r : Int) : 2 * triZ r = r * (r + 1) := by
  unfold triZ
  have h : 2 ∣ r * (r + 1) := two_dvd_mul_succ r
  exact Int.mul_ediv_cancel' h
```

The exact theorem may be named `Int.mul_ediv_cancel'`; if it is not, search for the lemma proving `a * (b / a) = b` under `a ∣ b`.  This is a small local obstacle, not a conceptual risk.

## Theorem 4: sign simplification

Do not use `(-1)^r` with negative integer exponents.  Prove parity equality instead.

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

theorem negOnePowInt_beta_a (k r : Int) :
    negOnePowInt r = negOnePowInt (r - 2*k) := by
  unfold negOnePowInt
  have h : r % 2 = (r - 2*k) % 2 := by omega
  simp [h]

end Ch10
end QseriesFormalization
```

If `omega` does not solve `%` goals over `Int`, use `Int.ModEq 2 r (r - 2*k)` and convert to equality of `negOnePowInt` by a helper lemma.

## Theorem 8: HM exponent matching

The HM exponent after substituting

```text
x = X,
y = -X^3,
q = X,
HM variables m=r, n=k
```

is

```text
r*(r+1)/2 + 3*r*k + 2*k^2 + k.
```

So the theorem is:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

def HMExp (k r : Int) : Int :=
  triZ r + 3 * r * k + 2 * k ^ 2 + k

theorem HMExp_eq_E (k r : Int) : HMExp k r = E k r := by
  unfold HMExp E
  ring_nf

end Ch10
end QseriesFormalization
```

This should be easy because both sides use `triZ r` directly; no division arithmetic is needed beyond definitional equality.

## Theorem 6: `eps*L ∩ L = empty`, `eps^6*L = L`

With custom `PhiInt`, the unit action is explicit:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2*x.b⟩

@[simp] theorem epsMul_a (x : PhiInt) : (epsMul x).a = x.a + x.b := rfl
@[simp] theorem epsMul_b (x : PhiInt) : (epsMul x).b = x.a + 2*x.b := rfl

theorem epsMul_coset_expr (x : PhiInt) :
    (epsMul x).b - 3*(epsMul x).a = -2*x.a - x.b := by
  unfold epsMul
  ring

end Ch10
end QseriesFormalization
```

For nonintersection, if `InL` is divisibility-based:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

theorem epsMul_not_mem_L_of_mem_L (x : PhiInt) (hx : InL_dvd x) :
    ¬ InL_dvd (epsMul x) := by
  intro hxe
  rcases hx with ⟨m, hm⟩
  rcases hxe with ⟨n, hn⟩
  unfold epsMul at hn
  -- hm: x.b - 3*x.a - 1 = 10*m
  -- hn: (x.a+2*x.b) - 3*(x.a+x.b) - 1 = 10*n
  -- combine to get impossible congruence `5*x.a = -2 mod 10`.
  omega

end Ch10
end QseriesFormalization
```

For `eps^6`, avoid generic exponentiation at first.  Define the sixfold action explicitly.

The matrix for `epsMul` is

```text
M = [[1,1],[1,2]].
```

Its sixth power is

```text
M^6 = [[89,144],[144,233]].
```

Thus define:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

def eps6Mul (x : PhiInt) : PhiInt :=
  ⟨89*x.a + 144*x.b, 144*x.a + 233*x.b⟩

theorem eps6Mul_preserves_L (x : PhiInt) (hx : InL_dvd x) : InL_dvd (eps6Mul x) := by
  rcases hx with ⟨m, hm⟩
  unfold InL_dvd eps6Mul
  -- Key identity:
  -- new_coset_minus_one = old_coset_minus_one + 10*(-12*a - 20*b).
  use m - 12*x.a - 20*x.b
  omega

end Ch10
end QseriesFormalization
```

## Theorem 7: order of `phi^2` in `(O_K/(2*sqrt5))^x`

This is the highest-risk Tier 2 theorem if you try to use actual `RingOfIntegers`, ideals, and quotient rings immediately.

### Recommended first formal target

Prove an explicit CRT-target theorem first:

```text
O_K/(2*sqrt5)  ≅  O_K/(2) × O_K/(sqrt5)  ≅  F4 × F5.
```

But in Lean, begin with just the target:

```text
epsCRT has order 6 in F4^× × (ZMod 5)^×.
```

Then later prove that this is the image of `eps` under the quotient isomorphism.

### F4 options

Option A: use Mathlib finite fields if convenient.  Possible imports to try:

```lean
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
```

Depending on Mathlib names, `GaloisField 2 2` may be available.  If names drift, this can become a time sink.

Option B: define `F4` manually.  This is more work up front but very robust for order-6 only.

Represent `F4 = F2[α]/(α^2+α+1)` as pairs over `ZMod 2`:

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization
namespace Ch10

structure F4 where
  c0 : ZMod 2
  c1 : ZMod 2
  deriving DecidableEq, Repr

namespace F4

instance : One F4 := ⟨⟨1, 0⟩⟩
instance : Mul F4 :=
  ⟨fun x y =>
    -- alpha^2 = alpha + 1 in characteristic 2.
    ⟨x.c0*y.c0 + x.c1*y.c1,
     x.c0*y.c1 + x.c1*y.c0 + x.c1*y.c1⟩⟩

def alpha : F4 := ⟨0, 1⟩
def eps2 : F4 := alpha * alpha

end F4
end Ch10
end QseriesFormalization
```

Then define the CRT target:

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization
namespace Ch10

abbrev CRTTarget := F4 × ZMod 5

def epsCRT : CRTTarget := (F4.eps2, (4 : ZMod 5))

end Ch10
end QseriesFormalization
```

Prove:

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization
namespace Ch10

theorem epsCRT_pow_six : epsCRT ^ 6 = 1 := by
  native_decide

theorem epsCRT_pow_one_ne_one : epsCRT ^ 1 ≠ 1 := by
  native_decide

theorem epsCRT_pow_two_ne_one : epsCRT ^ 2 ≠ 1 := by
  native_decide

theorem epsCRT_pow_three_ne_one : epsCRT ^ 3 ≠ 1 := by
  native_decide

end Ch10
end QseriesFormalization
```

You may need `BEq`, `DecidableEq`, and finite instances for the custom type if using `native_decide`.  Since this is only a four-element type, manual `rfl`/case proofs are also fine.

### Full ideal quotient theorem later

The full theorem should be broken into lemmas:

```text
sqrt5 = 2phi - 1.
O_K/(2) is F4 because x^2-x-1 becomes x^2+x+1 irreducible mod 2.
O_K/(sqrt5) is F5 because sqrt5=0 implies phi=1/2=3 mod 5.
(2) and (sqrt5) are coprime.
CRT gives quotient by product ideal.
eps maps to (alpha^2, -1).
order is lcm(3,2)=6.
```

This is mathematically clean but Lean-heavy.  Do not block Tier 1 on this.

## Theorem 5: exact coefficient formula

Tier 3 should be coefficient-level first, q-series-level second.

Define coefficient functions by finite support, not by infinite sums:

```lean
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

namespace QseriesFormalization
namespace Ch10

/-- A very safe finite bound for coefficient extraction. -/
def coeffBound (N : Nat) : Int := (N : Int) + 10

-- Later: Finset.Icc (-coeffBound N) (coeffBound N), filtered by cones and `E k r = N`.

end Ch10
end QseriesFormalization
```

But for general `N`, proving the bound is the real work.  The better staged approach is:

1. Define `AcoeffInBox bound N`, `DcoeffInBox bound N`, `BcoeffInBox bound N`.
2. Prove special values for Theorem 9 with a concrete bound, e.g. `bound=10`.
3. Later prove a general support-bound theorem and remove the box parameter.

The exact formula theorem should eventually say:

```text
B_N = sum over beta in L, -Norm(beta)=10N+1, beta in A or D cone of W(beta).
```

But in Lean this is easiest after you have:

```text
(k,r) <-> beta bijection
norm identity
sign simplification
cone predicates transported through inverse formulas
```

So Tier 3 is not conceptually hard; it is infrastructure-heavy.

## Theorem 9: explicit non-multiplicativity counterexample

Use the norm values:

```text
11 * 31 = 341
11 = 10*1 + 1
31 = 10*3 + 1
341 = 10*34 + 1
```

The coefficient values are:

```text
B_1  = 1
B_3  = -2
B_34 = 3
```

Thus

```text
B_34 != B_1 * B_3
```

because

```text
3 != -2.
```

### Manual coefficient proofs

For `B_1`:

```text
E(k,r)=1
A-cone solution: (k,r)=(0,1), weight +1
D-cone solutions: none
B_1=1
```

For `B_3`:

```text
E(k,r)=3
A-cone solutions: (k,r)=(1,0), (0,2), each weight -1
D-cone solutions: none
B_3=-2
```

For `B_34`:

```text
A-cone solution: (k,r)=(2,3), weight +1
D-cone solutions: (k,r)=(-1,-6), (-3,-2), each weight +1
B_34=3
```

This gives a no-q-series proof of nonmultiplicativity.

### Lean strategy

In actual final code, avoid difficult set extensionality if unnecessary.  Use bounded finite enumeration or dedicated uniqueness/exhaustion lemmas using `interval_cases`:

```lean
have hk_bound : 0 <= k ∧ k <= 4 := by nlinarith [...]
interval_cases k <;> interval_cases r <;> norm_num [E, triZ] at *
```

For D-cone, substitute

```text
k = -u - 1,
r = -v - 1,
u,v >= 0.
```

Then use the positive formula

```text
E(-u-1,-v-1)
  = 2*u^2 + 6*u + 3*u*v + (v^2 + 7*v)/2 + 4.
```

This is much easier for bounding.

## 5. Biggest risks and hardest parts

### Risk 1: treating `L` as a sublattice

`L` is an affine coset.  This affects type choices, unit action, and quotient statements.  Use a predicate or subtype.

### Risk 2: integer division in `E`

`triZ r = r*(r+1)/2` creates proof obligations.  Isolate them in two lemmas:

```text
2 ∣ r*(r+1)
2*triZ r = r*(r+1)
```

After that, polynomial proofs become routine.

### Risk 3: `(-1)^r` for negative `r`

Do not use integer exponentiation.  Define a parity sign function `negOnePowInt`.

### Risk 4: Theorem 7 if attempted too abstractly

`RingOfIntegers`, ideal quotients, finite fields, and CRT are all available in principle but will consume time.  Prove the explicit CRT-target order first.  Bridge to quotient ideals later.

### Risk 5: Theorem 5 finite support

The q-series exact formula needs a finite-support theorem for coefficient extraction.  For each fixed coefficient, cone positivity gives finiteness; but Lean needs explicit bounds.  Do special coefficients first, then generalize.

### Risk 6: `native_decide` over complicated structures

`native_decide` is great for finite custom rings and finite tables.  It is not a substitute for proving infinite cone bounds or coefficient formulas.

## 6. Alternative architectures

### Alternative A: `Zsqrtd 5`

Not recommended.  `Zsqrtd 5` models `Z[sqrt(5)]`, but the ring of integers is `Z[(1+sqrt(5))/2]`.  You would constantly fight factors of `2`.  The theorems are naturally in `(a,b)` coordinates for `a+b phi`, so this is the wrong abstraction for Tier 1.

### Alternative B: `NumberField.RingOfIntegers`

Mathematically canonical, but too heavy for the first implementation.  It is the right endpoint if you want the final theorem to literally mention `O_K`, ideals, quotient rings, and Hecke characters.  It is not the right starting point for polynomial identities, mod-10 cosets, and coefficient computations.

Recommended use:

```text
First prove everything in `PhiInt`.
Later define a map from `PhiInt` to `𝓞 (Q(sqrt 5))` and prove it is a ring equivalence.
Then transport high-level statements if needed.
```

### Alternative C: coordinates only, no ring type

This is viable and even simpler.  You can avoid `Mul PhiInt` entirely and just define:

```text
norm(a,b)
epsMul(a,b)
beta(k,r)
```

This is the most robust approach if the only goal is the nine theorems.  I still prefer `PhiInt` because the notation remains close to the mathematics and prepares for Theorem 7.

## 7. Recommended implementation order

### Phase 1: build pure algebra

```text
PhiInt.lean
ConeAlgebra.lean
```

Targets:

```text
Q_even
Q_eq_two_mul_E
beta_mem_L
exists_beta_of_mem_L
norm_beta
negOnePowInt_beta_a
HMExp_eq_E
epsMul_not_mem_L_of_mem_L
eps6Mul_preserves_L
```

### Phase 2: explicit nonmultiplicativity

```text
FiniteCounterexample.lean
```

Targets:

```text
Bcoeff_1 = 1
Bcoeff_3 = -2
Bcoeff_34 = 3
B_not_multiplicative_on_11_31
```

Use manual finite enumeration or interval cases.

### Phase 3: CRT order

```text
CRTOrder.lean
```

Targets:

```text
epsCRT^6 = 1
no smaller positive power is 1
```

Then, optionally:

```text
CRTTarget represents O_K/(2*sqrt5)
```

### Phase 4: coefficient formula bridge

```text
CoefficientFormula.lean
```

Targets:

```text
finite support lemmas for A/D cones
coefficient-level exact formula
bridge to existing q-series infrastructure
```

## 8. Suggested theorem names

Use names that describe the coordinate theorem, not the paper theorem number:

```text
Q_even
Q_eq_two_mul_E
beta_mem_L
exists_beta_of_mem_L
beta_injective
norm_beta
parity_beta_a
BWeight_eq_transported_weight
HMExp_eq_E
HMSign_eq_BSign
epsMul_not_preserve_L
eps6Mul_preserves_L
epsCRT_order_six
Bcoeff_one
Bcoeff_three
Bcoeff_thirty_four
B_not_multiplicative
```

Paper theorem numbers can be comments or aliases later.

## 9. A compact starter file

This is the core skeleton I would actually start with.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

namespace QseriesFormalization
namespace Ch10

structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

instance : Zero PhiInt := ⟨⟨0, 0⟩⟩
instance : One PhiInt := ⟨⟨1, 0⟩⟩
instance : Add PhiInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg PhiInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub PhiInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul PhiInt :=
  ⟨fun x y =>
    ⟨x.a * y.a + x.b * y.b,
     x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[ext] theorem ext (x y : PhiInt) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x
  cases y
  simp at ha hb
  simp [ha, hb]

def norm (x : PhiInt) : Int := x.a ^ 2 + x.a * x.b - x.b ^ 2

def phi : PhiInt := ⟨0, 1⟩
def sqrt5 : PhiInt := ⟨-1, 2⟩
def eps : PhiInt := ⟨1, 1⟩

end PhiInt

def Q (k r : Int) : Int :=
  4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r

def triZ (r : Int) : Int := r * (r + 1) / 2

def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

def beta (k r : Int) : PhiInt :=
  ⟨r - 2 * k, 4 * k + 3 * r + 1⟩

def InL (x : PhiInt) : Prop :=
  10 ∣ x.b - 3 * x.a - 1

def InACone (k r : Int) : Prop := 0 <= k ∧ 0 <= r
def InDCone (k r : Int) : Prop := k < 0 ∧ r < 0

def negOnePowInt (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2*x.b⟩

def eps6Mul (x : PhiInt) : PhiInt :=
  ⟨89*x.a + 144*x.b, 144*x.a + 233*x.b⟩

end Ch10
end QseriesFormalization
```

I would then add lemmas one at a time, building after each theorem.

## 10. Bottom line

The best architecture is a deliberately low-tech coordinate formalization.  It matches the mathematics, avoids algebraic-number-field overhead, and keeps the first six to eight theorems within reach of `simp`, `omega`, `ring_nf`, and `nlinarith`.

The two hardest parts are:

```text
Theorem 7, if stated directly using quotient ideals of the ring of integers;
Theorem 5, if stated directly as an equality of coefficients of infinite q-series.
```

Both should be staged through concrete coordinate/finite formulations first.  Once the coordinate theorems are stable, the high-level number-field and q-series bridges can be added without risking the algebraic core.
