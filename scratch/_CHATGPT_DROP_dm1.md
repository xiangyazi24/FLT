# Q3129 (dm1): Ch10 Lean Framework — Round 2

Date: 2026-07-02

## Executive answer

The main tactical recommendation is:

```text
Use the isolated `triZ` lemmas, not a doubled-only API.
```

The doubled identity `Q_eq_two_mul_E` is useful and should be part of the API, but it does not eliminate the `triZ` division issue because `norm_beta` is an undoubled theorem.  You eventually need a robust lemma proving

```lean
2 * triZ r = r * (r + 1)
```

anyway.

The most important correction is in Q3: the proposed statement

```text
eps^k * L ∩ L = empty for k = 1..5
```

is **false**.  It is true for `k=1,3,5`, but false for `k=2,4`.  A counterexample for `k=2` is

```text
x = 1 + 4 phi.
```

It lies in `L`, and `eps^2*x = 14 + 23 phi` also lies in `L`, because

```text
4 - 3*1 = 1,
23 - 3*14 = -19 ≡ 1 mod 10.
```

So do not build Lean around the five non-preservation theorem.  The correct unit-coset story is periodic/parity-dependent; `eps^6` preserves `L`, but smaller even powers can intersect `L` nontrivially.

## Q1. The `triZ` ediv landmine

Use approach B as the main proof style:

1. Prove `two_dvd_mul_succ_int`.
2. Prove `two_mul_triZ`.
3. Use `nlinarith [two_mul_triZ r]` for polynomial identities involving `E`.

Approach A, proving only `2 * E = Q`, is still worth adding as an API theorem, but it is not enough for `norm_beta` because the target is not doubled.

Here is a self-contained version of the proof.  It uses only `Mathlib.Tactic`; no `sorry`, no axiom, no number-field infrastructure.

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

/-- Norm in `Z[phi]`, where `phi^2 = phi + 1`. -/
def norm (x : PhiInt) : Int := x.a ^ 2 + x.a * x.b - x.b ^ 2

end PhiInt

/-- Twice the exponent. -/
def Q (k r : Int) : Int :=
  4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r

/-- Integer triangular number. -/
def triZ (r : Int) : Int := r * (r + 1) / 2

/-- The exponent. -/
def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

/-- Atom-to-`Z[phi]` map. -/
def beta (k r : Int) : PhiInt :=
  ⟨r - 2 * k, 4 * k + 3 * r + 1⟩

/-- Product of two consecutive integers is even. -/
lemma two_dvd_mul_succ_int (r : Int) : 2 ∣ r * (r + 1) := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with h | h
  · refine ⟨(r / 2) * (r + 1), ?_⟩
    have hr : r = 2 * (r / 2) := by omega
    rw [hr]
    ring
  · refine ⟨r * ((r + 1) / 2), ?_⟩
    have hr : r + 1 = 2 * ((r + 1) / 2) := by omega
    rw [hr]
    ring

/-- The key `triZ` cancellation lemma. -/
lemma two_mul_triZ (r : Int) : 2 * triZ r = r * (r + 1) := by
  unfold triZ
  rcases two_dvd_mul_succ_int r with ⟨t, ht⟩
  have hquot : r * (r + 1) / 2 = t := by omega
  rw [hquot, ht]
  ring

/-- Useful doubled API theorem. -/
theorem Q_eq_two_mul_E (k r : Int) : Q k r = 2 * E k r := by
  have htri : 2 * triZ r = r * (r + 1) := two_mul_triZ r
  unfold Q E triZ at *
  nlinarith

/-- The norm identity. -/
theorem norm_beta (k r : Int) :
    -PhiInt.norm (beta k r) = 10 * E k r + 1 := by
  have htri : 2 * triZ r = r * (r + 1) := two_mul_triZ r
  unfold PhiInt.norm beta E triZ at *
  nlinarith

end Ch10
end QseriesFormalization
```

Notes:

- This avoids depending on brittle lemma names such as `Int.ediv_mul_cancel`.
- The only moderately ambitious line is `have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega`.  In current Lean/Mathlib, `omega` is designed for this kind of Presburger/mod arithmetic.  If that line ever becomes brittle, replace it with Mathlib's explicit two-modulus lemma for integers, but keep the rest of the proof unchanged.
- Once `two_mul_triZ` exists, most polynomial identities involving `E` become one-liners with `nlinarith`.

## Q2. Theorem 9 box bounds and `B_1`

First separate the coefficient computation into two layers:

1. Prove solution-classification lemmas for `E(k,r)=N` in the A- and D-cones.
2. Use those lemmas to simplify the finite coefficient definition of `B_N`.

For `B_1`, the A-cone classification is:

```text
k >= 0, r >= 0, E(k,r)=1  iff  (k,r)=(0,1).
```

The D-cone is empty because after `k=-u-1`, `r=-v-1`, the D-cone exponent is at least `4`.

Here is a Lean-style interval proof for the A-cone classification.  It uses `Q_eq_two_mul_E` to avoid unfolding `triZ` until the final finite cases.

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

lemma A_E_one_solution (k r : Int)
    (hk : 0 <= k) (hr : 0 <= r) (hE : E k r = 1) :
    k = 0 ∧ r = 1 := by
  have hQ : Q k r = 2 := by
    have hQE : Q k r = 2 * E k r := Q_eq_two_mul_E k r
    omega

  -- Nonnegative product terms in the A-cone.
  have hkr0 : 0 <= k * r := mul_nonneg hk hr
  have h6kr0 : 0 <= 6 * k * r := by nlinarith

  -- From Q=2 and nonnegativity, get small finite bounds.
  have hk_le : k <= 1 := by
    unfold Q at hQ
    nlinarith [sq_nonneg k, sq_nonneg r, h6kr0, hk, hr]

  have hr_le : r <= 2 := by
    unfold Q at hQ
    have hr_le_term : r <= (6 * k + 1) * r := by nlinarith [h6kr0]
    nlinarith [sq_nonneg k, sq_nonneg r, hk, hr_le_term, hQ]

  interval_cases k <;> interval_cases r <;> norm_num [E, triZ] at hE ⊢

end Ch10
end QseriesFormalization
```

After

```lean
interval_cases k <;> interval_cases r
```

the proof has six concrete branches:

```text
k = 0, r = 0
k = 0, r = 1
k = 0, r = 2
k = 1, r = 0
k = 1, r = 1
k = 1, r = 2
```

The remaining goal in each branch is either:

```lean
⊢ 0 = 0 ∧ 1 = 1
```

for the true branch `(k,r)=(0,1)`, or a contradiction in `hE`, such as:

```lean
hE : 0 = 1
⊢ False / or an impossible coordinate equality goal
```

The final line

```lean
norm_num [E, triZ] at hE ⊢
```

closes all branches.

For the D-cone empty lemma, I would not try to reason directly with negative `k,r`.  Add a D-cone normalization lemma:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

/-- D-cone exponent after `k=-u-1`, `r=-v-1`. -/
lemma E_neg_succ_neg_succ (u v : Int) :
    E (-u - 1) (-v - 1)
      = 2 * u ^ 2 + 6 * u + 3 * u * v + (v ^ 2 + 7 * v) / 2 + 4 := by
  have htri : 2 * triZ (-v - 1) = (-v - 1) * (-v) := two_mul_triZ (-v - 1)
  unfold E triZ at *
  nlinarith

end Ch10
end QseriesFormalization
```

Then prove `D_E_one_empty` and `D_E_three_empty` by setting

```text
u = -k - 1,
v = -r - 1,
```

with `u,v >= 0`, and using the displayed formula.  For `N=1,3`, the constant `+4` alone gives the contradiction.  For `N=34`, the bounds you listed are reasonable:

```text
A-cone: k in [0,3], r in [0,7]
D-cone: u in [0,2], v in [0,5]
```

For the actual `B_1=1` theorem, once your finite coefficient function exists, the proof should be a rewrite from the two classification lemmas:

```lean
-- Schematic, because the exact name/shape of your coefficient definition is not fixed here.
theorem Bcoeff_one : Bcoeff 1 = 1 := by
  -- rewrite finite sum using A_E_one_solution and D_E_one_empty
  -- reduce the single surviving atom `(0,1)`
  norm_num [BWeight, negOnePowInt, E, triZ]
```

The key point is that the hard part is not the final arithmetic; it is the solution classification.  Do the classification lemmas first.

## Q3. Theorem 6 and powers of `eps`

Do **not** try to prove

```text
eps^k * L ∩ L = empty for k=1..5.
```

That statement is false.

### Counterexample for `k=2`

Define the second iterate explicitly:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

def InL (x : PhiInt) : Prop :=
  10 ∣ x.b - 3 * x.a - 1

def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2 * x.b⟩

def eps2Mul (x : PhiInt) : PhiInt :=
  epsMul (epsMul x)

example : eps2Mul ⟨1, 4⟩ = ⟨14, 23⟩ := by
  norm_num [eps2Mul, epsMul]

example : InL ⟨1, 4⟩ ∧ InL (eps2Mul ⟨1, 4⟩) := by
  constructor <;> norm_num [InL, eps2Mul, epsMul]

end Ch10
end QseriesFormalization
```

Mathematically:

```text
1 + 4 phi ∈ L,
eps^2(1+4phi) = 14 + 23phi ∈ L.
```

So `eps^2 L ∩ L` is nonempty.  Similarly, `eps^4 L ∩ L` is nonempty.  The empty cases are the odd powers `eps`, `eps^3`, and `eps^5`.

### Concrete proof for `k=1`

The `k=1` proof is clean with the divisibility-form `InL`.

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

def InL (x : PhiInt) : Prop :=
  10 ∣ x.b - 3 * x.a - 1

def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2 * x.b⟩

theorem epsMul_not_mem_L_of_mem_L (x : PhiInt) (hx : InL x) :
    ¬ InL (epsMul x) := by
  intro hxe
  rcases hx with ⟨m, hm⟩
  rcases hxe with ⟨n, hn⟩
  unfold epsMul at hn
  unfold InL at hm hn
  omega

end Ch10
end QseriesFormalization
```

This works because the two divisibility witnesses imply incompatible linear equations:

```text
x.b - 3*x.a - 1 = 10*m,
(x.a + 2*x.b) - 3*(x.a + x.b) - 1 = 10*n.
```

`omega` sees the contradiction.

### What to prove instead

Use explicit iterates and prove the true periodic behavior.

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

def eps2Mul (x : PhiInt) : PhiInt :=
  ⟨2 * x.a + 3 * x.b, 3 * x.a + 5 * x.b⟩

def eps3Mul (x : PhiInt) : PhiInt :=
  ⟨5 * x.a + 8 * x.b, 8 * x.a + 13 * x.b⟩

def eps4Mul (x : PhiInt) : PhiInt :=
  ⟨13 * x.a + 21 * x.b, 21 * x.a + 34 * x.b⟩

def eps5Mul (x : PhiInt) : PhiInt :=
  ⟨34 * x.a + 55 * x.b, 55 * x.a + 89 * x.b⟩

def eps6Mul (x : PhiInt) : PhiInt :=
  ⟨89 * x.a + 144 * x.b, 144 * x.a + 233 * x.b⟩

end Ch10
end QseriesFormalization
```

Then prove:

```text
eps^1 L ∩ L = empty,
eps^3 L ∩ L = empty,
eps^5 L ∩ L = empty,
eps^2 L ∩ L is nonempty,
eps^4 L ∩ L is nonempty,
eps^6 L = L.
```

For `eps^6`, the proof from R1 remains right:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

theorem eps6Mul_preserves_L (x : PhiInt) (hx : InL x) : InL (eps6Mul x) := by
  rcases hx with ⟨m, hm⟩
  unfold InL eps6Mul at *
  use m - 12 * x.a - 20 * x.b
  omega

end Ch10
end QseriesFormalization
```

I would use explicit `epskMul` definitions rather than repeated composition for these modular proofs.  Repeated composition with

```lean
simp [epsMul]
```

does reduce, but explicit iterates keep the goals small and make `omega` much happier.

The proposed `c = <-2,4>` divisibility trick is not the right first route, because the universal non-preservation statement it is meant to prove is false.  It may still be useful later for classifying which unit powers preserve which coset, but start with explicit matrices.

## Q4. The `@[ext]` theorem

Lean creates a structure extensionality theorem named something like `PhiInt.ext`, but I would still add an explicitly tagged theorem so the `ext` tactic is predictable in your namespace.

Use this:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

@[ext] theorem ext_coords (x y : PhiInt)
    (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      simp at ha hb
      subst ya
      subst yb
      rfl

end PhiInt

end Ch10
end QseriesFormalization
```

After this, if your goal is an equality of `PhiInt`s, use:

```lean
ext <;> simp [beta, epsMul, eps2Mul, eps6Mul] <;> omega
```

`omega` cannot solve a `PhiInt.mk ... = PhiInt.mk ...` goal directly.  It needs the goal split into coordinate equalities first.  After `ext`, the goals are integer equalities, and `omega` is appropriate.

Example:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2 * x.b⟩

def eps2Mul (x : PhiInt) : PhiInt :=
  epsMul (epsMul x)

theorem eps2Mul_formula (x : PhiInt) :
    eps2Mul x = ⟨2 * x.a + 3 * x.b, 3 * x.a + 5 * x.b⟩ := by
  ext <;> simp [eps2Mul, epsMul] <;> ring

end Ch10
end QseriesFormalization
```

You can use `ring` or `omega` after `ext`; for purely linear coordinate formulas, `omega` is usually enough.

## Final recommendations

1. Prove and use `two_mul_triZ`.  Keep `Q_eq_two_mul_E` too, but do not rely on doubled identities alone.
2. For small coefficient proofs, classify solutions first, then let the coefficient theorem be a finite-sum simplification.
3. Correct Theorem 6 before formalizing it: `eps^2 L ∩ L` and `eps^4 L ∩ L` are nonempty.  The safe theorem is `eps^1`, `eps^3`, `eps^5` are disjoint from `L`, and `eps^6` preserves `L`.
4. Add an explicit `@[ext]` theorem for `PhiInt`.  Then `ext <;> simp [...] <;> omega` is the standard pattern for coordinate equalities.

The biggest substantive fix is Q3.  If you formalize the false five-case theorem, Lean will correctly block you; the counterexample `⟨1,4⟩` should be added as a regression test.
