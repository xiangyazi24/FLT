# Q763 (dm3): formula-level `n`-fold projective addition over `CommRing`

## Bottom line

The approach is feasible as a **formula-level auxiliary**, but not with the exact recursion

```lean
def formulaNsmul (W : WeierstrassCurve R) : ℕ → (Fin 3 → R) → (Fin 3 → R)
  | 0, _ => ![0, 1, 0]
  | n+1, P => W.toProjective.addXYZ (formulaNsmul W n P) P
```

The obstruction is important: `Projective.addXYZ` is the **generic addition** formula for two distinct representatives.  Mathlib deliberately has a separate `Projective.dblXYZ` for doubling.  In fact `addXYZ P P = ![0,0,0]`, so a repeated-addition recursion that ever calls `addXYZ` on two scalar-multiple copies of the same representative collapses to the zero triple.

For the formal point

```text
P(t) = [t : -1 : w(t)]
```

the first step from the point at infinity is already dangerous.  The projective formula gives

```text
addXYZ O P = P_z • P
```

up to the standard theorem `addXYZ_of_Z_eq_zero_left`.  Here `P_z = w(t)`, and `w(t)` is not a unit in `PowerSeries R`.  Hence `P_z • P` is not equivalent to `P` in Mathlib's projective setoid, which only scales by units.  The next generic addition against `P` is a scalar-multiple self-addition and the homogeneity lemma `addXYZ_smul` reduces it to `addXYZ P P = 0`.

So the exact `addXYZ`-only recursion is not the right object for `[n]P` over `PowerSeries R` or over dual numbers.  The corrected version is: use a formula expression/addition chain with **explicit doubling nodes** and **explicit generic-addition nodes**, avoiding `addXYZ` whenever the two input formulae are known to represent the same multiple.

---

## What Mathlib already gives you

The relevant current Mathlib API is very favorable:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
```

Key definitions/lemmas in `WeierstrassCurve.Projective`:

```lean
-- generic addition formula; if the representatives are equal, this is zero
noncomputable def addXYZ (W : WeierstrassCurve.Projective R)
    (P Q : Fin 3 → R) : Fin 3 → R

-- doubling formula
noncomputable def dblXYZ (W : WeierstrassCurve.Projective R)
    (P : Fin 3 → R) : Fin 3 → R

@[simp]
lemma map_addXYZ (f : R →+* S) (P Q : Fin 3 → R) :
    (W.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ W.addXYZ P Q

@[simp]
lemma map_dblXYZ (f : R →+* S) (P : Fin 3 → R) :
    (W.map f).dblXYZ (f ∘ P) = f ∘ W.dblXYZ P

lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W.addXYZ P Q

lemma dblXYZ_smul (P : Fin 3 → R) (u : R) :
    W.dblXYZ (u • P) = u ^ 4 • W.dblXYZ P

lemma addXYZ_self (P : Fin 3 → R) :
    W.addXYZ P P = ![0, 0, 0]
```

This is exactly the split needed for a formula-level construction: `dblXYZ` for known self-additions, `addXYZ` for known distinct additions, and the map lemmas for base change to `K[ε]`.

---

## Recommended Lean shape: formula expressions, not naive recursion

Use an expression tree that records which formula is being applied.  This avoids any need to decide equality of projective representatives over a general ring.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

noncomputable section

namespace WeierstrassCurve
namespace ProjectiveFormula

abbrev Triple (R : Type*) := Fin 3 → R

/-- Formula expressions for projective multiples of a fixed base point.

`add A B` means: apply the generic two-input addition formula to the representatives
computed by `A` and `B`.  It should only be used in chains where the two multiples are
known generically distinct.  Use `dbl A` for self-addition. -/
inductive Expr : Type
  | O : Expr
  | P : Expr
  | dbl : Expr → Expr
  | add : Expr → Expr → Expr
  deriving Repr

namespace Expr

/-- The integer multiple represented by the expression, used only as bookkeeping. -/
def weight : Expr → ℕ
  | O => 0
  | P => 1
  | dbl A => 2 * weight A
  | add A B => weight A + weight B

/-- Evaluate a formula expression over any commutative ring. -/
def eval {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Projective R) (P : Triple R) : Expr → Triple R
  | O => ![0, 1, 0]
  | P => P
  | dbl A => W.dblXYZ (eval W P A)
  | add A B => W.addXYZ (eval W P A) (eval W P B)

@[simp]
theorem eval_O {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Projective R) (P : Triple R) :
    eval W P O = ![0, 1, 0] := rfl

@[simp]
theorem eval_P {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Projective R) (P : Triple R) :
    eval W P P = P := rfl

@[simp]
theorem eval_dbl {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Projective R) (P : Triple R) (A : Expr) :
    eval W P (dbl A) = W.dblXYZ (eval W P A) := rfl

@[simp]
theorem eval_add {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Projective R) (P : Triple R) (A B : Expr) :
    eval W P (add A B) = W.addXYZ (eval W P A) (eval W P B) := rfl

/-- Naturality/base-change of any formula expression.  This is the key transport
lemma for evaluating the same formula over `R`, `S`, `PowerSeries R`, or `K[ε]`. -/
@[simp]
theorem eval_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve.Projective R) (P : Triple R) :
    ∀ A : Expr,
      eval (W.map φ) (φ ∘ P) A = φ ∘ eval W P A := by
  intro A
  induction A with
  | O =>
      ext i <;> fin_cases i <;> simp [eval]
  | P =>
      rfl
  | dbl A ih =>
      simp [eval, ih]
  | add A B ihA ihB =>
      simp [eval, ihA, ihB]

/-- A compact binary-chain expression for small tests.  For serious proofs, make this
an explicit addition chain so its shape is stable under simp. -/
def two : Expr := dbl P

def three : Expr := add (dbl P) P

def four : Expr := dbl (dbl P)

def five : Expr := add (dbl (dbl P)) P

end Expr
end ProjectiveFormula
end WeierstrassCurve
```

This is the small core I would put in the repository first.  The important theorem is `Expr.eval_map`; it is the formula-level analogue of naturality and should be robust because Mathlib marks `map_dblXYZ` and `map_addXYZ` as simp lemmas.

---

## What `formulaNsmul` should be

For a usable `formulaNsmul`, do not define it by linear recursion through `O + P`.  Use one of these two patterns.

### Pattern A: explicit addition chains

For each fixed `n` needed in the Mortenson/division-polynomial proof, define an expression:

```lean
def expr2 : Expr := Expr.dbl Expr.P
def expr3 : Expr := Expr.add (Expr.dbl Expr.P) Expr.P
def expr4 : Expr := Expr.dbl (Expr.dbl Expr.P)
def expr5 : Expr := Expr.add (Expr.dbl (Expr.dbl Expr.P)) Expr.P
```

Then evaluate by

```lean
Expr.eval W.toProjective P exprN
```

This is the best route if the proof only needs a finite list of small `n`, or if `preΨ' n` is also being developed recursively along the same chain.

### Pattern B: a recursive binary chain

If you need arbitrary `n`, build a chain by recursion on `n`, but make the branch produce `dbl` for even steps and `add _ P` for odd steps.  The actual implementation should be an expression-valued function, not a direct triple-valued function:

```lean
-- schematic shape, not meant as the final termination proof
def nsmulExpr : ℕ → Expr
  | 0 => Expr.O
  | 1 => Expr.P
  | 2 => Expr.dbl Expr.P
  | n + 3 =>
      if h : Even (n + 3) then
        Expr.dbl (nsmulExpr ((n + 3) / 2))
      else
        Expr.add (nsmulExpr (n + 2)) Expr.P
```

In the actual Lean file I would use either a well-founded definition on `<` or avoid cleverness and define an addition-chain data structure with a proof that every reference points backward.  That gives you clean induction principles for both naturality and leading-term proofs.

---

## Relation to the formal group

This approach can bridge to the formal group, but the bridge is not just `Z`-coordinate inspection.  You need a normalization layer.

For the formal point

```text
P(t) = [t : -1 : w(t)]
```

the affine/formal local coordinates are recovered on the chart where the `Y`-coordinate is a unit:

```text
t(P) = -X / Y,
w(P) = -Z / Y.
```

Over `PowerSeries R`, division here means multiplication by the inverse of the unit `Y`.  Thus the right target statement should usually be normalized:

```text
normalizeY(Q) := (-Q_Y)⁻¹ • Q
```

or, more Lean-friendly, define only the two local functions

```lean
localT(Q) = - Q 0 * (Q 1)⁻¹
localW(Q) = - Q 2 * (Q 1)⁻¹
```

where `(Q 1)⁻¹` is available after proving `Q 1` is a unit in `PowerSeries R`.

Then the bridge theorem should look like:

```text
localT (Expr.eval W P (nsmulExpr n)) = formalGroupMul W n t
localW (Expr.eval W P (nsmulExpr n)) = formalW evaluated at formalGroupMul W n t
```

up to any scalar factor introduced by the formula expression.  The raw projective triple produced by `dblXYZ`/`addXYZ` is homogeneous and may carry nonunit scalar factors.  Those scalar factors do not matter after `Y`-normalization if the `Y`-coordinate is a unit, but they absolutely matter for a raw statement about the `Z`-component.

This is also where the expected relation with `preΨ' n` should be stated carefully.  A raw formula `Z`-coordinate often contains division-polynomial factors and expression-dependent homogeneous scaling factors.  The invariant statement is usually one of:

```text
Z_n = unit_or_known_factor * preΨ'(n) * known_power_of_w_or_t
```

or

```text
localW(Q_n) = -Z_n / Y_n = formalW([n]_F t).
```

The second statement is normally easier to connect to the formal group; the first statement is the stronger division-polynomial bookkeeping theorem.

---

## Infrastructure needed in Lean

### 1. Formula expression evaluator

Implement `Expr` and `Expr.eval` as above.  Prove once:

```lean
Expr.eval_map
```

This gives universal transport to every base ring, including `PowerSeries R` and dual numbers.

### 2. Homogeneity/scaling bookkeeping

Use Mathlib's existing lemmas:

```lean
dblXYZ_smul : W.dblXYZ (u • P) = u ^ 4 • W.dblXYZ P
addXYZ_smul : W.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W.addXYZ P Q
```

For expression trees, define a scaling exponent function if needed:

```text
scaleWeight(dbl A)    = 4 * scaleWeight(A)
scaleWeight(add A B)  = 2 * scaleWeight(A) + 2 * scaleWeight(B)
```

or more concretely prove expression-specific lemmas for the chains you use.  This is necessary because nonunit scalar factors over `PowerSeries R` cannot be ignored as projective equivalences.

### 3. Formal point package

Bundle the formal point and its equation proof:

```lean
def formalPoint (W : WeierstrassCurve R) : Fin 3 → PowerSeries R :=
  ![PowerSeries.X, -1, W.formalW]
```

Then prove:

```text
W.toProjective.Equation (formalPoint W)
(formalPoint W) 1 is a unit
```

The second is immediate from coefficient/constant-term facts because the `Y` coordinate is `-1`.

### 4. Unit criterion for power series

You will repeatedly need:

```text
IsUnit f ↔ IsUnit (PowerSeries.constantCoeff R f)
```

or the local theorem available in your Mathlib snapshot.  Use this to show the `Y`-coordinate of the evaluated expression remains a unit for the formal multiples you care about.

### 5. Local-coordinate normalization

Define local coordinates only under a unit hypothesis:

```lean
noncomputable def localT {R : Type*} [CommRing R]
    (Q : Fin 3 → PowerSeries R) (hY : IsUnit (Q 1)) : PowerSeries R :=
  -Q 0 * hY.unit⁻¹

noncomputable def localW {R : Type*} [CommRing R]
    (Q : Fin 3 → PowerSeries R) (hY : IsUnit (Q 1)) : PowerSeries R :=
  -Q 2 * hY.unit⁻¹
```

Depending on your local API, the exact coercion from `hY.unit⁻¹` may need `((hY.unit⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)`.

### 6. Leading-term API

For the `Z`-component leading statement, avoid depending on a global valuation API at first.  Define a simple coefficient-level predicate:

```lean
def HasLeadingTerm {R : Type*} [CommRing R]
    (f : PowerSeries R) (k : ℕ) (u : R) : Prop :=
  PowerSeries.coeff R k f = u ∧ IsUnit u ∧ ∀ m < k, PowerSeries.coeff R m f = 0
```

Then prove closure lemmas:

```text
HasLeadingTerm f a u → HasLeadingTerm g b v → HasLeadingTerm (f * g) (a+b) (u*v)
HasLeadingTerm f a u → HasLeadingTerm (f^k) (a*k) (u^k)
HasLeadingTerm f a u → IsUnit c → HasLeadingTerm (c • f) a (c*u)
```

This is enough to state and prove claims like

```text
HasLeadingTerm ((Expr.eval W P exprN) 2) (n^2) unitCoeff
```

without first importing a valuation theory.

### 7. Dual-number / `K[ε]` transport

Once `Expr.eval_map` exists, transport to dual numbers is formal.  Let `ι : K →+* Kε` be the scalar inclusion.  Then:

```text
Expr.eval ((W.map ι).toProjective) (ι ∘ P) A
  = ι ∘ Expr.eval W.toProjective P A
```

For a genuine infinitesimal point over `K[ε]`, define it directly and use the same evaluator.  The connection to the formal group derivative then goes through `localT`, not through raw projective equality.

---

## Suggested theorem targets

I would add theorem targets in this order.

```lean
-- 1. Formula-level naturality.
theorem Expr.eval_map ...

-- 2. Formal point lies on the curve.
theorem formalPoint_equation ...

-- 3. The evaluated formula still has unit Y-coordinate for each fixed expression.
theorem eval_Y_isUnit_for_exprN ...

-- 4. Normalized local parameter agrees with formal-group multiplication.
theorem localT_eval_exprN_eq_formalMul ...

-- 5. Only after that, prove the raw Z/preΨ' relation.
theorem eval_Z_exprN_eq_prePsi_factor ...

-- 6. Convert the equality into a leading-term statement.
theorem eval_Z_exprN_hasLeadingTerm ...
```

The hardest step is not defining formula evaluation; it is proving theorem 4 or theorem 5.  The map/naturality part is easy because Mathlib already supplies the map lemmas for `dblXYZ` and `addXYZ`.

---

## Practical recommendation

Use `Projective.addXYZ` and `Projective.dblXYZ` as a low-level formula language, not as a naive `nsmul` function.  Define an explicit addition-chain expression for `[n]P`, prove `eval_map` once, normalize by the `Y`-coordinate to compare with the formal group, and separately track the homogeneous scalar factors if you need a raw `Z`-coordinate/preΨ' theorem.

That route is feasible and probably a good way to connect formula-level division-polynomial identities with universal formal-group transport.  The only thing I would avoid is the `addXYZ`-only recursion from `O`, because over `PowerSeries R` the nonunit scaling by `w(t)` makes it collapse almost immediately.