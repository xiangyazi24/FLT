# Q96 dm4 — Slim Weil-pairing interface for Mazur torsion bound

This note scopes the A2 residual seam

```lean
rationalWeilPairingPackage
```

for the Mazur torsion-finiteness / primitive-root step.  The key point is that the downstream primitive-root argument does **not** need the full geometric Weil-pairing construction if the package already produces a pairing valued in rational roots of unity:

```lean
E[n] × E[n] → rootsOfUnity n ℚ
```

Galois equivariance is construction-side infrastructure, not downstream proof-side infrastructure, once the codomain is already `ℚ`.

---

## 1. Minimal downstream interface

Assume `E/ℚ` has full rational `n`-torsion, packaged as an additive equivalence

```lean
(ZMod n × ZMod n) ≃+ E.nTorsion n.
```

The primitive-root argument uses only the following facts about a pairing `e`:

1. `e P Q ∈ μ_n(ℚ)`, i.e. the value is a member of `rootsOfUnity n ℚ`.
2. Additivity in the left variable.
3. Additivity in the right variable.
4. Alternating/self-triviality: `e P P = 1`.
5. Nondegeneracy restricted to the full rational grid:
   if `e (grid z) (grid w) = 1` for all grid points `w`, then `z = 0`.

It does **not** consume the following, provided the pairing already lands in `rootsOfUnity n ℚ`:

```lean
σ (e P Q) = e (σ P) (σ Q)
```

and it does not use a special relation of the form `e(P, σP)`.  That relation is relevant only in variants where one works over `AlgebraicClosure ℚ` first and then descends the value to `ℚ` using rationality of torsion points.

The absolute minimum could be made even slimmer: for a fixed full grid it is enough to know that

```lean
ζ := e (grid (1, 0)) (grid (0, 1))
```

has exact order `n`.  But that would hide all the mathematics in a single field.  The useful slim package is the alternating bimultiplicative pairing plus grid nondegeneracy.

---

## 2. Suggested Lean interface

This is the interface I would keep downstream.  It deliberately omits Galois equivariance.

```lean
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Instances.ZMod

open scoped Classical

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]

/-- Local abbreviation if the project does not already import `FLT.EllipticCurve.Torsion`. -/
abbrev nTorsion (n : ℕ) : Type :=
  Submodule.torsionBy ℤ (E⁄ℚ).Point n

/-- Full rational `n`-torsion as a chosen grid.  This is stronger and cleaner than merely
storing an injection into points. -/
structure HasFullRationalTorsion (n : ℕ) where
  gridEquiv : (ZMod n × ZMod n) ≃+ E.nTorsion n

namespace HasFullRationalTorsion

variable {E} {n : ℕ} (H : E.HasFullRationalTorsion n)

@[simp] def grid (z : ZMod n × ZMod n) : E.nTorsion n :=
  H.gridEquiv z

lemma grid_injective : Function.Injective H.grid :=
  H.gridEquiv.injective

lemma grid_surjective : Function.Surjective H.grid :=
  H.gridEquiv.surjective

end HasFullRationalTorsion

/-- Slim rational Weil-pairing package sufficient for the primitive-root argument. -/
structure WeilPairingPackage (n : ℕ) [NeZero n] where
  pairing : E.nTorsion n → E.nTorsion n → rootsOfUnity n ℚ
  map_add_left : ∀ P P' Q,
    pairing (P + P') Q = pairing P Q * pairing P' Q
  map_add_right : ∀ P Q Q',
    pairing P (Q + Q') = pairing P Q * pairing P Q'
  alternating : ∀ P,
    pairing P P = 1
  nondeg_left_on_full_grid :
    ∀ H : E.HasFullRationalTorsion n,
    ∀ z : ZMod n × ZMod n,
      (∀ w : ZMod n × ZMod n,
        pairing (H.grid z) (H.grid w) = 1) →
      z = 0

namespace WeilPairingPackage

variable {E} {n : ℕ} [NeZero n]
variable (W : E.WeilPairingPackage n)

/-- The value that should become a primitive rational `n`-th root of unity. -/
noncomputable def gridZeta (H : E.HasFullRationalTorsion n) : rootsOfUnity n ℚ :=
  W.pairing (H.grid (1, 0)) (H.grid (0, 1))

/-- Additivity gives the usual natural-scalar law in the left variable. -/
theorem map_nsmul_left (k : ℕ) (P Q : E.nTorsion n) :
    W.pairing (k • P) Q = W.pairing P Q ^ k := by
  induction k with
  | zero =>
      -- needs `pairing 0 Q = 1`, derived from `0 + 0 = 0` and cancellation in `rootsOfUnity`.
      -- Prove once as a helper lemma:
      --   pairing_zero_left : W.pairing 0 Q = 1
      sorry
  | succ k ih =>
      rw [succ_nsmul, W.map_add_left, ih, pow_succ]

/-- Additivity gives the usual natural-scalar law in the right variable. -/
theorem map_nsmul_right (k : ℕ) (P Q : E.nTorsion n) :
    W.pairing P (k • Q) = W.pairing P Q ^ k := by
  induction k with
  | zero =>
      -- analogous helper:
      --   pairing_zero_right : W.pairing P 0 = 1
      sorry
  | succ k ih =>
      rw [succ_nsmul, W.map_add_right, ih, pow_succ]

/-- Downstream primitive-root statement in order-of-units form.

This is the exact theorem consumed by the rational-root obstruction.  In Mathlib one can then
convert to `IsPrimitiveRoot (((W.gridZeta H : ℚˣ) : ℚ)) n` using the local primitive-root API. -/
theorem orderOf_gridZeta
    (H : E.HasFullRationalTorsion n) :
    orderOf (W.gridZeta H : ℚˣ) = n := by
  classical
  -- Skeleton:
  -- 1. `orderOf ζ ∣ n` because `ζ ∈ rootsOfUnity n ℚ`, i.e. `ζ ^ n = 1`.
  -- 2. For the reverse divisibility, let `k = orderOf ζ`.
  -- 3. Since `ζ ^ k = 1`, bilinearity implies
  --      e (k • grid (1,0)) (grid (a,b)) = 1
  --    for every `(a,b)`:
  --      e(kP, aP + bQ) = e(kP,aP) * e(kP,bQ)
  --                      = 1 * (e(P,Q)^k)^b = 1.
  --    Here `e(kP,aP)=1` follows from alternating plus bilinearity.
  -- 4. Grid nondegeneracy gives `k • (1,0) = 0` in `ZMod n × ZMod n`.
  -- 5. Hence `(k : ZMod n) = 0`, so `n ∣ k`.
  -- 6. Combine both divisibilities by `Nat.dvd_antisymm`.
  sorry

end WeilPairingPackage
end WeierstrassCurve
```

### Why `nondeg_left_on_full_grid` is enough

A full global statement

```lean
∀ P : E.nTorsion n, (∀ Q, e P Q = 1) → P = 0
```

is stronger than necessary.  The primitive-root proof only needs to apply nondegeneracy to elements already known to lie in the chosen full rational grid.  Therefore this restricted field is enough:

```lean
nondeg_left_on_full_grid :
  ∀ H : E.HasFullRationalTorsion n,
  ∀ z : ZMod n × ZMod n,
    (∀ w : ZMod n × ZMod n,
      pairing (H.grid z) (H.grid w) = 1) →
    z = 0
```

If a construction proves full nondegeneracy, the restricted version is a two-line wrapper:

```lean
theorem nondeg_left_on_full_grid_of_nondeg_left
    {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
    {n : ℕ} [NeZero n]
    (e : E.nTorsion n → E.nTorsion n → rootsOfUnity n ℚ)
    (hnd : ∀ P : E.nTorsion n, (∀ Q, e P Q = 1) → P = 0)
    (H : E.HasFullRationalTorsion n)
    (z : ZMod n × ZMod n)
    (hz : ∀ w : ZMod n × ZMod n, e (H.grid z) (H.grid w) = 1) :
    z = 0 := by
  have hP : H.grid z = 0 := by
    apply hnd
    intro Q
    rcases H.grid_surjective Q with ⟨w, rfl⟩
    exact hz w
  exact H.grid_injective (by simpa using hP)
```

---

## 3. Does current Mathlib have Weil-pairing infrastructure?

I would treat the answer as **no** for the purposes of this project.

Current nearby API:

```lean
rootsOfUnity n R
mem_rootsOfUnity
rootsOfUnity.mkOfPowEq
rootsOfUnity.coe_mkOfPowEq
rootsOfUnity.coe_injective
restrictRootsOfUnity
MulEquiv.restrictRootsOfUnity
```

from

```lean
Mathlib.RingTheory.RootsOfUnity.Basic
```

Mathlib also has the affine elliptic-curve point group and explicit group law:

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
```

with important names such as:

```lean
WeierstrassCurve.Affine.Point
WeierstrassCurve.Affine.Point.instAddCommGroup
WeierstrassCurve.Affine.Point.map
WeierstrassCurve.Affine.negY
WeierstrassCurve.Affine.slope
WeierstrassCurve.Affine.addX
```

The FLT repo already adds or can add the natural torsion abbreviation:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and a `ZMod n` module structure on `E.nTorsion n` via `AddCommGroup.zmodModule`.

There is field-theoretic Kummer-extension infrastructure in Mathlib, but not an elliptic-curve Kummer sequence / Selmer group / Weil pairing on abelian varieties package sufficient to get the Weil pairing for `WeierstrassCurve`.  I also would not assume any abelian-variety-level Weil-pairing API is available for this use.

The closest reusable ingredients are therefore:

```lean
-- roots of unity
rootsOfUnity
rootsOfUnity.mkOfPowEq
restrictRootsOfUnity

-- elliptic points
WeierstrassCurve.Affine.Point
WeierstrassCurve.Affine.Point.map
WeierstrassCurve.Affine.Point.instAddCommGroup

-- torsion as algebra
Submodule.torsionBy
AddCommGroup.zmodModule
ZMod

-- explicit formulas
WeierstrassCurve.Affine.slope
WeierstrassCurve.Affine.addX
WeierstrassCurve.Affine.negY
```

Missing for the Weil pairing:

```lean
-- divisor theory on `WeierstrassCurve` points/function field
Divisor of rational functions on an elliptic curve
principal divisor API for explicit line/vertical functions
function evaluation on degree-zero divisors with disjoint support
Miller functions `f_{n,P}` with `div f = n[P] - n[O]`
tame symbols on the curve
Weil reciprocity for those functions
nondegeneracy of the constructed pairing
Galois-equivariance/descent if constructing over `AlgebraicClosure ℚ`
```

---

## 4. Miller construction vs cohomological construction

### Route A: Miller / rational functions with prescribed divisors

This is the more feasible route in current Mathlib because it can be built directly on the explicit Weierstrass-curve point API.  It is still substantial, but it is locally structured.

Milestones:

```lean
-- A. purely syntactic divisors on points
abbrev DivExpr := ((E⁄K).Point →₀ ℤ)

-- B. syntactic rational functions used by Miller
inductive MillerExpr
  | one
  | const : Kˣ → MillerExpr
  | line : Point → Point → MillerExpr
  | vertical : Point → MillerExpr
  | mul : MillerExpr → MillerExpr → MillerExpr
  | inv : MillerExpr → MillerExpr

-- C. divisor expression attached to a Miller expression
MillerExpr.divExpr : MillerExpr → DivExpr

-- D. evaluation on degree-zero divisors with disjoint support
MillerExpr.evalDiv :
  (f : MillerExpr) →
  (D : DivExpr) →
  degree D = 0 →
  Disjoint (divExpr f).support D.support →
  Kˣ

-- E. Miller recurrence
millerNat : ℕ → Point → MillerExpr

theorem divExpr_millerNat_torsion
  (P : E.nTorsion n) :
  divExpr (millerNat n P.1) =
    (n : ℤ) • [P] - (n : ℤ) • [O]

-- F. Weil reciprocity for Miller expressions
theorem weil_reciprocity_millerExpr :
  evalDiv f (divExpr g) _ _ = evalDiv g (divExpr f) _ _

-- G. pairing and proofs
rationalWeilPairing : E.nTorsion n → E.nTorsion n → rootsOfUnity n ℚ
```

The hard primitives are:

```lean
-- line and vertical divisor formulae
div(line(P,Q)) = [P] + [Q] + [-(P+Q)] - 3[O]
div(vertical(P)) = [P] + [-P] - 2[O]

-- Weil reciprocity, usually via tame symbols
weil_reciprocity_millerExpr

-- nondegeneracy of the pairing
rationalWeilPairing_nondeg_left
```

This is where the earlier “multi-week” estimate is accurate.  The syntactic wrapper files are not hard; the divisor formulae, tame-symbol reciprocity, and nondegeneracy are the real cost.

A realistic focused estimate:

```text
DivExpr/MillerExpr/evalDiv bookkeeping:        days to 1 week
line/vertical divisor formulae:                1+ week, coordinate-heavy
Miller recurrence divisor theorem:             days after divisor formulae
Weil reciprocity/tame symbols:                 1–2+ weeks
nondegeneracy/cardinality/perfectness:          1–2+ weeks, depending on torsion-cardinality API
rational descent / Galois equivariance:         days if point-map/Galois action is in place
```

Total: multi-week, plausibly 4–8 focused weeks, not a local seam discharge.

### Route B: Galois-cohomological / cup-product construction

This is less feasible in current Mathlib for this project.  It wants substantially more global infrastructure:

```lean
finite flat / étale group schemes or at least finite Galois modules
elliptic Kummer sequence
connecting homomorphism E(K)/nE(K) → H¹(K,E[n])
μ_n and cup products
Weil pairing as a perfect alternating pairing of finite group schemes
compatibility with torsion and Galois action
```

Even if some general group-cohomology or field-theoretic Kummer files exist, this route does not avoid the need to identify the elliptic curve’s `n`-torsion dual with `μ_n` through the Weil pairing.  For the present goal, it is a research-level infrastructure route, not the shortest path.

Conclusion: use the Miller route if the package is to be constructed; otherwise keep the full construction as a named seam and expose the slim rational package downstream.

---

## 5. Construction skeleton for the feasible Miller route

The construction should not be placed directly in the Mazur proof file.  Build the following layers.

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

/-- Formal divisors supported on affine nonsingular points. -/
abbrev DivExpr : Type _ :=
  ((E⁄K).Point →₀ ℤ)

namespace DivExpr

noncomputable def degree (D : E.DivExpr) : ℤ :=
  D.sum fun _ n => n

def point (P : (E⁄K).Point) : E.DivExpr :=
  Finsupp.single P 1

def disjoint (D₁ D₂ : E.DivExpr) : Prop :=
  Disjoint D₁.support D₂.support

end DivExpr

/-- Syntactic expressions for the rational functions used in Miller's algorithm. -/
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
      -- [P] + [Q] + [-(P+Q)] - 3[O]
      sorry
  | vertical P =>
      -- [P] + [-P] - 2[O]
      sorry
  | mul f g => divExpr f + divExpr g
  | inv f => - divExpr f

/-- Evaluation of a Miller expression on a degree-zero divisor with disjoint support. -/
noncomputable def evalDiv
    (f : E.MillerExpr) (D : E.DivExpr)
    (hdeg : E.DivExpr.degree D = 0)
    (hdisj : Disjoint (divExpr (E := E) f).support D.support) : Kˣ :=
  sorry

/-- The hard reciprocity primitive. -/
theorem weil_reciprocity_millerExpr
    (f g : E.MillerExpr)
    (hfg : Disjoint (divExpr (E := E) f).support (divExpr (E := E) g).support) :
    evalDiv (E := E) f (divExpr (E := E) g) (by sorry) hfg =
    evalDiv (E := E) g (divExpr (E := E) f) (by sorry) hfg.symm := by
  sorry

/-- Miller function `f_{n,P}`. -/
noncomputable def millerNat
    (n : ℕ) (P : (E⁄K).Point) : E.MillerExpr :=
  sorry

/-- Divisor of the Miller function for a torsion point. -/
theorem divExpr_millerNat_torsion
    {n : ℕ} [NeZero n] (P : E.nTorsion n) :
    divExpr (E := E) (millerNat (E := E) n P.1) =
      (n : ℤ) • DivExpr.point (E := E) P.1
        - (n : ℤ) • DivExpr.point (E := E) 0 := by
  sorry

end MillerExpr
end WeierstrassCurve
```

Then the rational pairing layer:

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
variable (n : ℕ) [NeZero n]

/-- Raw Miller-Weil value before packaging as a root of unity. -/
noncomputable def millerWeilValue
    (P Q : E.nTorsion n) : ℚˣ :=
  sorry

theorem millerWeilValue_pow_eq_one
    (P Q : E.nTorsion n) :
    ((millerWeilValue (E := E) n P Q : ℚˣ) : ℚ) ^ n = 1 := by
  -- Uses Miller divisor theorem and Weil reciprocity.
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

theorem rationalWeilPairing_nondeg_left_on_full_grid
    (H : E.HasFullRationalTorsion n)
    (z : ZMod n × ZMod n)
    (hz : ∀ w : ZMod n × ZMod n,
      rationalWeilPairing (E := E) n (H.grid z) (H.grid w) = 1) :
    z = 0 := by
  -- Either prove directly from the Miller pairing's nondegeneracy or wrap full nondegeneracy.
  sorry

noncomputable def rationalWeilPairingPackage :
    E.WeilPairingPackage n where
  pairing := rationalWeilPairing (E := E) n
  map_add_left := rationalWeilPairing_map_add_left (E := E) n
  map_add_right := rationalWeilPairing_map_add_right (E := E) n
  alternating := rationalWeilPairing_alternating (E := E) n
  nondeg_left_on_full_grid := rationalWeilPairing_nondeg_left_on_full_grid (E := E) n

end WeierstrassCurve
```

---

## 6. If constructing first over `AlgebraicClosure ℚ`

If the first available construction is geometric,

```lean
Ē[n] × Ē[n] → rootsOfUnity n (AlgebraicClosure ℚ),
```

then the package needs an extra construction-side descent lemma:

```lean
theorem geometricWeilPairing_galois_equivariant
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P Q : Ebar.nTorsion n) :
    restrictRootsOfUnity (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) n
      (geometricPairing P Q)
    = geometricPairing (σ • P) (σ • Q) := by
  sorry

theorem geometricPairing_of_rational_torsion_is_rational
    (P Q : E.nTorsion n) :
    ∃ ζ : rootsOfUnity n ℚ,
      mapRootsToAlgebraicClosure ζ =
        geometricPairing (baseChangeTors P) (baseChangeTors Q) := by
  -- rationality of P,Q plus Galois equivariance plus fixed-field theorem
  sorry
```

That descent layer is avoidable downstream if `rationalWeilPairingPackage` is taken as the seam.

---

## 7. Recommended seam boundary

Use this as the named A2 residual seam:

```lean
noncomputable def rationalWeilPairingPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
    (n : ℕ) [NeZero n] :
    E.WeilPairingPackage n :=
  sorry
```

Do **not** put Miller/tame-symbol/nondegeneracy details in the Mazur proof file.  The Mazur file should consume only:

```lean
W.pairing
W.map_add_left
W.map_add_right
W.alternating
W.nondeg_left_on_full_grid
```

and then prove:

```lean
full rational n-torsion on E/ℚ
  ⟹ ∃ ζ : rootsOfUnity n ℚ, orderOf (ζ : ℚˣ) = n
  ⟹ ℚ contains a primitive n-th root of unity
  ⟹ n ≤ 2, or the appropriate rational-root obstruction used in the torsion bound.
```

This keeps the formal dependency honest and makes the future construction route clear.
