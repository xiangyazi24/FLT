/-
  scratch/ProjectiveFormula.lean
  Projective division-polynomial Z-component formulas.

  ATOM 3a: addZ(![C X, y, 1], ![W.φ m, ω, W.ψ m]) = W.ψ (m - 1) * W.ψ (m + 1)
  ATOM 3b: dblZ_W.toPoly(![W.φ m, W.ωP m, W.ψ m]) = W.ψ (2 * m)

  The addZ identity is a RAW polynomial equality (φ_m unfolds directly).
  The dblZ identity requires lifting W to R[X][Y] via `map` since dblZ uses
  the curve coefficients a₁, a₃, and uses the ωP normalization identity.

  Status: 0 sorry, 0 axiom.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.Tactic

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial

/-! ## ATOM 3a: Z-component addition formula -/

section AddZFormula

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **ATOM 3a.** The Z-coordinate of the Jacobian addition `P + R_m` equals
`ψ_{m-1} * ψ_{m+1}`, where `P = ![C X, y_val, 1]` is a generic affine point
and `R_m = ![φ_m, ω, ψ_m]` is the division-polynomial representative.

The Y-coordinates are irrelevant: `addZ` depends only on X- and Z-coordinates.

Proof: unfold `φ_m := C(X) * ψ_m² - ψ_{m+1} * ψ_{m-1}` and cancel. -/
theorem addZ_divPoly_eq (m : ℤ) (y_val ω : R[X][X]) :
    addZ (![Polynomial.C (Polynomial.X : R[X]), y_val, 1])
         (![W.φ m, ω, W.ψ m]) =
      W.ψ (m - 1) * W.ψ (m + 1) := by
  unfold addZ WeierstrassCurve.φ; simp; ring

end AddZFormula

/-! ## ATOM 3b: Z-component doubling formula -/

section DblZFormula

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The Weierstrass curve lifted to the bivariate polynomial ring `R[X][Y]`
via the double constant embedding `r ↦ C(C(r))`. -/
noncomputable abbrev WeierstrassCurve.toPoly : WeierstrassCurve R[X][X] :=
  W.map ((Polynomial.C : R[X] →+* R[X][X]).comp (Polynomial.C : R →+* R[X]))

/-- The complement factor witnessing `ψ_n ∣ ψ_{2n}` in `R[X][Y]`,
defined via the elliptic divisibility sequence complement `complEDS₂`. -/
noncomputable def WeierstrassCurve.ψTwoMulQuotP (n : ℤ) : R[X][X] :=
  complEDS₂ W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) n

/-- `ψ_n * ψTwoMulQuotP n = ψ_{2n}`. -/
theorem WeierstrassCurve.ψ_mul_ψTwoMulQuotP (n : ℤ) :
    W.ψ n * W.ψTwoMulQuotP n = W.ψ (2 * n) := by
  simp only [WeierstrassCurve.ψ, WeierstrassCurve.ψTwoMulQuotP]
  exact normEDS_mul_complEDS₂ W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) n

/-- The division polynomial `ω_m ∈ R[X][Y]`, defined with `Invertible (2 : R)`.
Satisfies `2 * ψ_m * ω_m = ψ_{2m} - ψ_m² * (a₁ * φ_m + a₃ * ψ_m²)`. -/
noncomputable def WeierstrassCurve.ωP [Invertible (2 : R)] (n : ℤ) : R[X][X] :=
  Polynomial.C (Polynomial.C (⅟(2 : R))) * (W.ψTwoMulQuotP n -
    W.ψ n * (Polynomial.C (Polynomial.C W.a₁) * W.φ n +
             Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2))

/-- The cleared normalization identity:
`C(C 2) * ψ_n * ωP n = ψ_{2n} - ψ_n² * (C(C a₁) * φ_n + C(C a₃) * ψ_n²)`. -/
theorem WeierstrassCurve.two_mul_ψ_mul_ωP [Invertible (2 : R)] (n : ℤ) :
    Polynomial.C (Polynomial.C (2 : R)) * W.ψ n * W.ωP n =
      W.ψ (2 * n) - W.ψ n ^ 2 *
        (Polynomial.C (Polynomial.C W.a₁) * W.φ n +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2) := by
  unfold WeierstrassCurve.ωP
  rw [← W.ψ_mul_ψTwoMulQuotP]
  have hcancel : Polynomial.C (Polynomial.C (2 : R)) *
      Polynomial.C (Polynomial.C (⅟(2 : R))) = (1 : R[X][X]) := by
    rw [← map_mul, ← map_mul, mul_invOf_self, map_one, map_one]
  calc Polynomial.C (Polynomial.C (2 : R)) * W.ψ n *
      (Polynomial.C (Polynomial.C (⅟(2 : R))) *
        (W.ψTwoMulQuotP n - W.ψ n *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ n +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2)))
      = Polynomial.C (Polynomial.C (2 : R)) * Polynomial.C (Polynomial.C (⅟(2 : R))) *
        W.ψ n * (W.ψTwoMulQuotP n - W.ψ n *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ n +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2)) := by ring
    _ = 1 * W.ψ n * (W.ψTwoMulQuotP n - W.ψ n *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ n +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2)) := by rw [hcancel]
    _ = W.ψ n * W.ψTwoMulQuotP n - W.ψ n ^ 2 *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ n +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2) := by ring

/-- **ATOM 3b.** The Z-coordinate of the Jacobian doubling `2 • R_m` equals `ψ_{2m}`,
where `R_m = ![φ_m, ωP_m, ψ_m]` and the curve is lifted to `R[X][Y]` via `toPoly`.

Proof: expand `dblZ(R_m) = ψ_m * (ωP_m − negY(R_m))`, simplify negY, then apply
the normalization identity `C(C 2) * ψ_m * ωP_m = ψ_{2m} − ...`. -/
theorem dblZ_divPoly_eq [Invertible (2 : R)] (m : ℤ) :
    W.toPoly.toJacobian.dblZ (![W.φ m, W.ωP m, W.ψ m]) = W.ψ (2 * m) := by
  simp only [WeierstrassCurve.Jacobian.dblZ, WeierstrassCurve.Jacobian.negY,
    WeierstrassCurve.toPoly, WeierstrassCurve.map]
  simp
  have h := W.two_mul_ψ_mul_ωP m
  have h2 : (2 : R[X][X]) = Polynomial.C (Polynomial.C (2 : R)) := by
    simp [map_ofNat]
  linear_combination (norm := ring_nf) h + (W.ψ m * W.ωP m) * h2

end DblZFormula

-- Axiom audit
#print axioms addZ_divPoly_eq
#print axioms dblZ_divPoly_eq

