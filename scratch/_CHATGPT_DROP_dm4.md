# Q100 dm4 — Build-ready slim Weil-pairing scaffold

This is the round-2 version of the A2 residual interface.  The goal is to make the downstream Mazur primitive-root argument depend on the smallest stable API, while leaving the construction of the Weil pairing as a named deep seam.

The important design choice is:

*The downstream primitive-root argument does not need Galois equivariance if the pairing is already rational-valued.*

So the seam should provide

```lean
E[n] × E[n] → rootsOfUnity n ℚ
```

with bilinearity, alternating/self-triviality, and nondegeneracy on the chosen full rational grid.  Galois equivariance is only needed behind the seam if the construction is first carried out over `AlgebraicClosure ℚ`.

---

## 1. Minimal Lean interface

In the FLT repo this should live after importing the existing torsion file, which defines

```lean
WeierstrassCurve.nTorsion
```

as

```lean
Submodule.torsionBy ℤ (E⁄K).Point n
```

The exact minimal package is this:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Instances.ZMod

open scoped Classical

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]

/-- A chosen full rational `n`-torsion grid.  This is the preferred downstream shape.
It is deliberately an additive equivalence, not merely an injection into points. -/
abbrev FullRationalTorsionGrid (n : ℕ) : Type :=
  (ZMod n × ZMod n) ≃+ E.nTorsion n

/-- Minimal rational Weil-pairing package consumed by the Mazur primitive-root argument.

No Galois-equivariance field appears here: the codomain is already `rootsOfUnity n ℚ`.
If the construction is geometric over `AlgebraicClosure ℚ`, Galois equivariance belongs in the
construction layer that descends the geometric pairing to this rational-valued package. -/
structure WeilPairingPackage (n : ℕ) [NeZero n] where
  /-- The rational-valued `n`-Weil pairing. -/
  pairing : E.nTorsion n → E.nTorsion n → rootsOfUnity n ℚ

  /-- Additivity in the first variable. -/
  map_add_left :
    ∀ P P' Q : E.nTorsion n,
      pairing (P + P') Q = pairing P Q * pairing P' Q

  /-- Additivity in the second variable. -/
  map_add_right :
    ∀ P Q Q' : E.nTorsion n,
      pairing P (Q + Q') = pairing P Q * pairing P Q'

  /-- Alternating in the only form needed downstream. -/
  alternating :
    ∀ P : E.nTorsion n,
      pairing P P = 1

  /-- Nondegeneracy restricted to a full rational torsion grid.

  This is weaker than global nondegeneracy but exactly what the primitive-root proof consumes. -/
  nondeg_left_on_full_grid :
    ∀ grid : E.FullRationalTorsionGrid n,
    ∀ z : ZMod n × ZMod n,
      (∀ w : ZMod n × ZMod n,
        pairing (grid z) (grid w) = 1) →
      z = 0

namespace WeilPairingPackage

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
variable {n : ℕ} [NeZero n]
variable (W : E.WeilPairingPackage n)

@[simp] theorem pairing_zero_left (Q : E.nTorsion n) :
    W.pairing 0 Q = 1 := by
  have h := W.map_add_left 0 0 Q
  have h1 : (1 : rootsOfUnity n ℚ) = W.pairing 0 Q := by
    simpa [mul_assoc] using congrArg (fun x => (W.pairing 0 Q)⁻¹ * x) h
  exact h1.symm

@[simp] theorem pairing_zero_right (P : E.nTorsion n) :
    W.pairing P 0 = 1 := by
  have h := W.map_add_right P 0 0
  have h1 : (1 : rootsOfUnity n ℚ) = W.pairing P 0 := by
    simpa [mul_assoc] using congrArg (fun x => (W.pairing P 0)⁻¹ * x) h
  exact h1.symm

/-- Natural-scalar law in the first variable. -/
theorem pairing_nsmul_left (k : ℕ) (P Q : E.nTorsion n) :
    W.pairing (k • P) Q = W.pairing P Q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_eq_add_one, add_nsmul, one_nsmul, W.map_add_left, ih, pow_succ]

/-- Natural-scalar law in the second variable. -/
theorem pairing_nsmul_right (k : ℕ) (P Q : E.nTorsion n) :
    W.pairing P (k • Q) = W.pairing P Q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_eq_add_one, add_nsmul, one_nsmul, W.map_add_right, ih, pow_succ]

/-- The distinguished pairing value attached to a full torsion grid. -/
noncomputable def gridZeta (grid : E.FullRationalTorsionGrid n) : rootsOfUnity n ℚ :=
  W.pairing (grid (1, 0)) (grid (0, 1))

/-- This is the exact downstream primitive-root extraction target.

This theorem is closeable from the package plus elementary `ZMod` algebra.  It is separated from
the package so the package stays minimal. -/
theorem exists_rootOfUnity_of_full_grid
    (grid : E.FullRationalTorsionGrid n) :
    ∃ ζ : rootsOfUnity n ℚ, orderOf (ζ : ℚˣ) = n := by
  classical
  refine ⟨W.gridZeta grid, ?_⟩
  /-
  Proof skeleton, all downstream and not part of the package fields.

  Let `P = grid (1,0)`, `Q = grid (0,1)`, and `ζ = e P Q`.

  1. `orderOf (ζ : ℚˣ) ∣ n` because `ζ ∈ rootsOfUnity n ℚ`.
     This uses `mem_rootsOfUnity` / the subtype property of `rootsOfUnity` and
     `orderOf_dvd_of_pow_eq_one`.

  2. Put `k = orderOf (ζ : ℚˣ)`.  Then `ζ^k = 1`.

  3. Prove
       `∀ w, e (grid ((k : ℕ) • (1,0))) (grid w) = 1`.
     Decompose `w : ZMod n × ZMod n` as `(a,0) + (0,b)`.
     Use `grid.map_add`, `map_add_right`, `map_add_left`, `alternating`, and
     the scalar lemmas above.  The `(a,0)` contribution is killed by alternating;
     the `(0,b)` contribution is killed by `ζ^k = 1`.

  4. Apply `nondeg_left_on_full_grid` to get
       `(k : ℕ) • (1,0) = 0` in `ZMod n × ZMod n`.

  5. Read off the first coordinate to get `(k : ZMod n) = 0`, hence `n ∣ k`.

  6. Combine `k ∣ n` and `n ∣ k` by `Nat.dvd_antisymm`.

  Possible helper declarations to close before this theorem:

    theorem zmod_natCast_eq_zero_iff_dvd
      {n k : ℕ} : (k : ZMod n) = 0 ↔ n ∣ k

    theorem fullGrid_apply_pair
      (grid : E.FullRationalTorsionGrid n) (a b : ZMod n) :
        grid (a,b) = grid (a,0) + grid (0,b)

    theorem fullGrid_apply_first_zmod_smul
      (grid : E.FullRationalTorsionGrid n) (a : ZMod n) :
        grid (a,0) = a • grid (1,0)

    theorem fullGrid_apply_second_zmod_smul
      (grid : E.FullRationalTorsionGrid n) (b : ZMod n) :
        grid (0,b) = b • grid (0,1)
  -/
  sorry

end WeilPairingPackage
end WeierstrassCurve
```

### Why this is minimal

The package omits all of the following because the primitive-root argument does not consume them once the pairing is rational-valued:

```lean
-- not needed downstream
pairing_galois_equivariant :
  ∀ σ P Q, σ (pairing P Q) = pairing (σ • P) (σ • Q)

-- not needed downstream
skew_symm : ∀ P Q, pairing Q P = (pairing P Q)⁻¹

-- not needed downstream if `nondeg_left_on_full_grid` is present
nondeg_left : ∀ P, (∀ Q, pairing P Q = 1) → P = 0
nondeg_right : ∀ Q, (∀ P, pairing P Q = 1) → Q = 0
```

The absolute logical minimum for the Mazur obstruction would be even smaller:

```lean
structure PrimitiveRootFromFullTorsion (n : ℕ) [NeZero n] where
  zeta : rootsOfUnity n ℚ
  orderOf_zeta : orderOf (zeta : ℚˣ) = n
```

But that would no longer be recognizably a Weil-pairing seam.  The `WeilPairingPackage` above is the minimal mathematically transparent interface.

---

## 2. Closeable-now downstream helpers

These are not construction of the Weil pairing.  They are package-consumer lemmas and should be discharged before touching Miller functions.

### CLOSEABLE-NOW: full-grid nondegeneracy wrapper

If a future construction proves full left nondegeneracy, this converts it to the package field.

```lean
theorem nondeg_left_on_full_grid_of_nondeg_left
    {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
    {n : ℕ} [NeZero n]
    (e : E.nTorsion n → E.nTorsion n → rootsOfUnity n ℚ)
    (hnd : ∀ P : E.nTorsion n, (∀ Q : E.nTorsion n, e P Q = 1) → P = 0)
    (grid : E.FullRationalTorsionGrid n)
    (z : ZMod n × ZMod n)
    (hz : ∀ w : ZMod n × ZMod n, e (grid z) (grid w) = 1) :
    z = 0 := by
  have hzP : grid z = 0 := by
    apply hnd
    intro Q
    rcases grid.surjective Q with ⟨w, rfl⟩
    exact hz w
  exact grid.injective (by simpa using hzP)
```

### CLOSEABLE-NOW: zero and scalar lemmas

Already included above:

```lean
WeilPairingPackage.pairing_zero_left
WeilPairingPackage.pairing_zero_right
WeilPairingPackage.pairing_nsmul_left
WeilPairingPackage.pairing_nsmul_right
```

### CLOSEABLE-NOW: primitive-root extraction

The theorem

```lean
WeilPairingPackage.exists_rootOfUnity_of_full_grid
```

is closeable after the following elementary `ZMod`/grid helpers are added locally if not already available:

```lean
theorem zmod_natCast_eq_zero_iff_dvd
    {n k : ℕ} : (k : ZMod n) = 0 ↔ n ∣ k := by
  -- likely already available under a nearby `ZMod` name;
  -- otherwise prove from `ZMod.natCast_eq_natCast_iff` with the RHS specialized to `0`.
  sorry

theorem fullGrid_apply_pair
    {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
    {n : ℕ} (grid : E.FullRationalTorsionGrid n) (a b : ZMod n) :
    grid (a,b) = grid (a,0) + grid (0,b) := by
  simpa using grid.map_add (a,0) (0,b)
```

The two `ZMod`-scalar grid lemmas are also elementary, but exact proof names depend on the imported module structure:

```lean
theorem fullGrid_apply_first_zmod_smul
    {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
    {n : ℕ} (grid : E.FullRationalTorsionGrid n) (a : ZMod n) :
    grid (a,0) = a • grid (1,0) := by
  -- close with `map_smul` once both sides are seen as `ZMod n` modules,
  -- or prove by induction/quotient on `a : ZMod n`.
  sorry

theorem fullGrid_apply_second_zmod_smul
    {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
    {n : ℕ} (grid : E.FullRationalTorsionGrid n) (b : ZMod n) :
    grid (0,b) = b • grid (0,1) := by
  sorry
```

---

## 3. Route comparison: Miller vs Galois-cohomology/Kummer

### More feasible route: Miller / explicit rational functions

Use Miller.  It is closer to current Mathlib because Mathlib has explicit Weierstrass curves, affine points, and the group law.  It still lacks divisor/reciprocity infrastructure, but the missing pieces are local and nameable.

### Less feasible route: Galois cohomology / Kummer

The Kummer route would be elegant on paper but is currently too infrastructure-heavy.  It requires elliptic Kummer sequences, Galois cohomology, cup products, and identification of the cup-product pairing with the Weil pairing.  That is broader than the A2 seam.

---

## 4. Miller route: build-ready scaffold with milestone status

### M1. Formal point divisors

**Status: CLOSEABLE-NOW**

This is pure `Finsupp` bookkeeping.

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

/-- Formal divisors supported on rational affine nonsingular points. -/
abbrev DivExpr : Type _ :=
  ((E⁄K).Point →₀ ℤ)

namespace DivExpr

noncomputable def degree (D : E.DivExpr) : ℤ :=
  D.sum fun _ n => n

def point (P : (E⁄K).Point) : E.DivExpr :=
  Finsupp.single P 1

def disjoint (D₁ D₂ : E.DivExpr) : Prop :=
  Disjoint D₁.support D₂.support

@[simp] theorem degree_zero : degree (E := E) 0 = 0 := by
  simp [degree]

@[simp] theorem degree_point (P : (E⁄K).Point) :
    degree (E := E) (point (E := E) P) = 1 := by
  classical
  simp [degree, point]

end DivExpr
end WeierstrassCurve
```

Missing declarations: none.  This is local project code.

---

### M2. Syntactic Miller expressions and formal divisors

**Status: CLOSEABLE-NOW for syntax; MISSING-MATHLIB-API for semantic divisor correctness**

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

inductive MillerExpr : Type _
  | one : MillerExpr
  | const : Kˣ → MillerExpr
  | line : (E⁄K).Point → (E⁄K).Point → MillerExpr
  | vertical : (E⁄K).Point → MillerExpr
  | mul : MillerExpr → MillerExpr → MillerExpr
  | inv : MillerExpr → MillerExpr

namespace MillerExpr

noncomputable def divExpr : E.MillerExpr → E.DivExpr
  | one => 0
  | const _ => 0
  | line P Q =>
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) Q +
      DivExpr.point (E := E) (-(P + Q)) -
      (3 : ℤ) • DivExpr.point (E := E) 0
  | vertical P =>
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) (-P) -
      (2 : ℤ) • DivExpr.point (E := E) 0
  | mul f g => divExpr f + divExpr g
  | inv f => - divExpr f

end MillerExpr
end WeierstrassCurve
```

Missing Mathlib/API declarations for the semantic layer:

```lean
-- proposed names; not currently available as Mathlib API
WeierstrassCurve.FunctionField
WeierstrassCurve.RationalFunction.divisor
WeierstrassCurve.RationalFunction.line
WeierstrassCurve.RationalFunction.vertical
WeierstrassCurve.divisor_line
WeierstrassCurve.divisor_vertical
```

Required statements:

```lean
theorem divisor_line
    (P Q : (E⁄K).Point) :
    divisor (lineFunction E P Q) =
      [P] + [Q] + [-(P+Q)] - 3 • [0] := by
  sorry

theorem divisor_vertical
    (P : (E⁄K).Point) :
    divisor (verticalFunction E P) =
      [P] + [-P] - 2 • [0] := by
  sorry
```

---

### M3. Evaluation on degree-zero divisors

**Status: CLOSEABLE-NOW for formal product algebra if `evalUnitAt` is abstracted; MISSING-MATHLIB-API for actual rational-function evaluation**

```lean
namespace WeierstrassCurve.MillerExpr

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

/-- Evaluation of a syntactic Miller expression at a point outside its divisor support. -/
noncomputable def evalUnitAt
    (f : E.MillerExpr) (P : (E⁄K).Point)
    (hP : P ∉ (divExpr (E := E) f).support) : Kˣ :=
  sorry

/-- Evaluation of a Miller expression on a degree-zero divisor with disjoint support. -/
noncomputable def evalDiv
    (f : E.MillerExpr) (D : E.DivExpr)
    (hdeg : DivExpr.degree (E := E) D = 0)
    (hdisj : Disjoint (divExpr (E := E) f).support D.support) : Kˣ :=
  sorry

end WeierstrassCurve.MillerExpr
```

Missing Mathlib/API declarations:

```lean
WeierstrassCurve.RationalFunction.evalAtPoint
WeierstrassCurve.RationalFunction.evalAtPoint_ne_zero_of_not_mem_support
WeierstrassCurve.evalDiv
WeierstrassCurve.evalDiv_add
WeierstrassCurve.evalDiv_mul
WeierstrassCurve.evalDiv_principal
```

Local closeable lemmas once `evalUnitAt` is available:

```lean
MillerExpr.evalDiv_zero
MillerExpr.evalDiv_add
MillerExpr.evalDiv_mul
MillerExpr.evalDiv_inv
MillerExpr.evalDiv_const_of_degree_zero
```

---

### M4. Miller recurrence

**Status: CLOSEABLE-NOW once M2 is in place**

The recurrence itself is formal algebra on the syntactic divisors.

```lean
namespace WeierstrassCurve.MillerExpr

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

noncomputable def addStepExpr
    (P Q : (E⁄K).Point) : E.MillerExpr :=
  .mul (.line P Q) (.inv (.vertical (P + Q)))

theorem divExpr_addStepExpr
    (P Q : (E⁄K).Point) :
    divExpr (E := E) (addStepExpr (E := E) P Q) =
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) Q -
      DivExpr.point (E := E) (P + Q) -
      DivExpr.point (E := E) 0 := by
  -- pure simplification from `divExpr`; some `Finsupp` abelian-group cleanup.
  sorry

noncomputable def millerNat
    (m : ℕ) (P : (E⁄K).Point) : E.MillerExpr :=
  match m with
  | 0 => .one
  | 1 => .one
  | k + 2 =>
      .mul (millerNat (E := E) (k + 1) P)
        (addStepExpr (E := E) ((k + 1 : ℕ) • P) P)

theorem divExpr_millerNat_torsion
    {m : ℕ} [NeZero m] (P : E.nTorsion m) :
    divExpr (E := E) (millerNat (E := E) m P.1) =
      (m : ℤ) • DivExpr.point (E := E) P.1 -
      (m : ℤ) • DivExpr.point (E := E) 0 := by
  -- induction on `m`; use `P.property : m • P.1 = 0`.
  sorry

end WeierstrassCurve.MillerExpr
```

Missing declarations: none beyond the torsion API already in FLT.  This is a local formal proof after M2.

---

### M5. Weil reciprocity for Miller expressions

**Status: MISSING-MATHLIB-API**

This is one of the deepest missing pieces.

Proposed declaration:

```lean
namespace WeierstrassCurve.MillerExpr

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

theorem weil_reciprocity_millerExpr
    (f g : E.MillerExpr)
    (hfg : Disjoint (divExpr (E := E) f).support (divExpr (E := E) g).support) :
    evalDiv (E := E) f (divExpr (E := E) g) (by sorry) hfg =
    evalDiv (E := E) g (divExpr (E := E) f) (by sorry) hfg.symm := by
  sorry

end WeierstrassCurve.MillerExpr
```

Missing Mathlib/API declarations needed to prove it semantically:

```lean
WeierstrassCurve.localParameter
WeierstrassCurve.orderAt
WeierstrassCurve.tameSymbol
WeierstrassCurve.tameSymbol_finite_support
WeierstrassCurve.product_tameSymbol_eq_one
WeierstrassCurve.weil_reciprocity
WeierstrassCurve.MillerExpr.weil_reciprocity_millerExpr
```

This is not closeable from current elliptic-curve point formulas alone.

---

### M6. Pairing construction and package wrapper

**Status: CLOSEABLE-NOW as a wrapper after M3–M5; MISSING-MATHLIB-API for nondegeneracy**

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
variable (n : ℕ) [NeZero n]

noncomputable def millerWeilValue
    (P Q : E.nTorsion n) : ℚˣ :=
  sorry

theorem millerWeilValue_pow_eq_one
    (P Q : E.nTorsion n) :
    ((millerWeilValue (E := E) n P Q : ℚˣ) : ℚ) ^ n = 1 := by
  -- uses Miller divisor theorem and `weil_reciprocity_millerExpr`
  sorry

noncomputable def rationalWeilPairing
    (P Q : E.nTorsion n) : rootsOfUnity n ℚ :=
  rootsOfUnity.mkOfPowEq
    ((millerWeilValue (E := E) n P Q : ℚˣ) : ℚ)
    (millerWeilValue_pow_eq_one (E := E) n P Q)

theorem rationalWeilPairing_map_add_left
    (P P' Q : E.nTorsion n) :
    rationalWeilPairing (E := E) n (P + P') Q =
      rationalWeilPairing (E := E) n P Q *
      rationalWeilPairing (E := E) n P' Q := by
  apply rootsOfUnity.coe_injective
  -- reduce to `millerWeilValue_map_add_left`
  sorry

theorem rationalWeilPairing_map_add_right
    (P Q Q' : E.nTorsion n) :
    rationalWeilPairing (E := E) n P (Q + Q') =
      rationalWeilPairing (E := E) n P Q *
      rationalWeilPairing (E := E) n P Q' := by
  apply rootsOfUnity.coe_injective
  sorry

theorem rationalWeilPairing_alternating
    (P : E.nTorsion n) :
    rationalWeilPairing (E := E) n P P = 1 := by
  apply rootsOfUnity.coe_injective
  sorry

/-- Preferred strong construction theorem; package uses only the full-grid corollary. -/
theorem rationalWeilPairing_nondeg_left
    (P : E.nTorsion n)
    (hP : ∀ Q : E.nTorsion n,
      rationalWeilPairing (E := E) n P Q = 1) :
    P = 0 := by
  sorry

theorem rationalWeilPairing_nondeg_left_on_full_grid
    (grid : E.FullRationalTorsionGrid n)
    (z : ZMod n × ZMod n)
    (hz : ∀ w : ZMod n × ZMod n,
      rationalWeilPairing (E := E) n (grid z) (grid w) = 1) :
    z = 0 :=
  nondeg_left_on_full_grid_of_nondeg_left
    (E := E) (n := n)
    (rationalWeilPairing (E := E) n)
    (rationalWeilPairing_nondeg_left (E := E) n)
    grid z hz

noncomputable def rationalWeilPairingPackage :
    E.WeilPairingPackage n where
  pairing := rationalWeilPairing (E := E) n
  map_add_left := rationalWeilPairing_map_add_left (E := E) n
  map_add_right := rationalWeilPairing_map_add_right (E := E) n
  alternating := rationalWeilPairing_alternating (E := E) n
  nondeg_left_on_full_grid := rationalWeilPairing_nondeg_left_on_full_grid (E := E) n

end WeierstrassCurve
```

Missing Mathlib/API declarations:

```lean
WeierstrassCurve.rationalWeilPairing
WeierstrassCurve.rationalWeilPairing_map_add_left
WeierstrassCurve.rationalWeilPairing_map_add_right
WeierstrassCurve.rationalWeilPairing_alternating
WeierstrassCurve.rationalWeilPairing_nondeg_left
WeierstrassCurve.rationalWeilPairingPackage
```

The first four are construction-level after reciprocity; nondegeneracy is a separate deep theorem.

---

## 5. Galois/Kummer route scaffold and why it is not the preferred path

**Status: MISSING-MATHLIB-API at almost every step**

A cohomological construction would want declarations like these:

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
variable (n : ℕ) [NeZero n]

-- proposed API, not current usable Mathlib API for this target
abbrev GeometricNTorsion : Type :=
  ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n)

/-- Kummer connecting map for the exact sequence `0 → E[n] → E → E → 0`. -/
noncomputable def kummerConnecting :
    sorry :=
  sorry

/-- Cup product pairing in Galois cohomology. -/
noncomputable def galoisCupProduct :
    sorry :=
  sorry

/-- Weil pairing as the perfect pairing identifying `E[n]` with the Cartier dual. -/
noncomputable def cohomologicalWeilPairing :
    GeometricNTorsion (E := E) n →
    GeometricNTorsion (E := E) n →
    rootsOfUnity n (AlgebraicClosure ℚ) :=
  sorry

/-- Galois equivariance needed to descend rational torsion values. -/
theorem cohomologicalWeilPairing_galois_equivariant :
    sorry := by
  sorry

/-- Descent of the geometric value to a rational root of unity when both torsion points are rational. -/
theorem cohomologicalWeilPairing_descends_to_rat
    (P Q : E.nTorsion n) :
    ∃ ζ : rootsOfUnity n ℚ,
      sorry = cohomologicalWeilPairing (E := E) n sorry sorry := by
  sorry

end WeierstrassCurve
```

Exact missing declarations/packages for the Kummer route:

```lean
GaloisCohomology.H1
GaloisCohomology.cupProduct
GaloisCohomology.kummerConnecting
WeierstrassCurve.kummerExactSequence
WeierstrassCurve.kummerConnecting
WeierstrassCurve.nTorsionCartierDual
WeierstrassCurve.cohomologicalWeilPairing
WeierstrassCurve.cohomologicalWeilPairing_galois_equivariant
WeierstrassCurve.cohomologicalWeilPairing_descends_to_rat
```

Even if some general cohomology files exist under different names, the elliptic-curve-specific Kummer sequence and duality statements above are not available as a ready API for this project.  Therefore this route is not the shortest way to discharge A2.

---

## 6. Final recommendation

Use the slim package as the downstream seam:

```lean
noncomputable def rationalWeilPairingPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
    (n : ℕ) [NeZero n] :
    E.WeilPairingPackage n :=
  sorry
```

Downstream Mazur should only consume:

```lean
W.pairing
W.map_add_left
W.map_add_right
W.alternating
W.nondeg_left_on_full_grid
```

and the closeable helper theorem:

```lean
W.exists_rootOfUnity_of_full_grid
```

The construction route should be Miller/Route-B.  The current honest hard seams are exactly:

```lean
WeierstrassCurve.divisor_line
WeierstrassCurve.divisor_vertical
WeierstrassCurve.MillerExpr.evalUnitAt
WeierstrassCurve.MillerExpr.weil_reciprocity_millerExpr
WeierstrassCurve.rationalWeilPairing_nondeg_left
```

Everything else is either package-wrapper work or `Finsupp`/`ZMod` algebra and is closeable now.
