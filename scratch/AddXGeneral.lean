/-
  scratch/AddXGeneral.lean
  General-m X-component projective identity.
  ATOM 4a (general m): mk(addX(P, R_m) - ψ_{m-1}² · φ_{m+1}) = 0
-/

import scratch.ProjectiveFormula
import scratch.ProjectiveFormulaXY
import scratch.PsiInvariant
import scratch.AddXGeneral_probe2
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial

section Helpers
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
private theorem ψ₂_expl :
    W.ψ 2 = 2 * (Polynomial.X : R[X][X]) +
    Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
    Polynomial.C (Polynomial.C W.a₃) := by
  rw [ψ_two]; unfold WeierstrassCurve.ψ₂ Affine.polynomialY; simp [map_ofNat]; ring
end Helpers

section GeneralM

variable {R : Type*} [CommRing R] [IsDomain R] [Invertible (2 : R)]
  (W : WeierstrassCurve R)

-- ω elimination (same pattern as m=2)
set_option maxHeartbeats 32000000 in
omit [IsDomain R] in
private theorem addX_elim_ω_gen (m : ℤ) :
    Polynomial.C (Polynomial.C (2 : R)) *
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) -
       W.ψ (m - 1) ^ 2 * W.φ (m + 1)) =
    Polynomial.C (Polynomial.C (2 : R)) *
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, 0, W.ψ m]) -
       W.ψ (m - 1) ^ 2 * W.φ (m + 1)) -
    W.ψ 2 * (W.ψ (2 * m) - W.ψ m ^ 2 *
        (Polynomial.C (Polynomial.C W.a₁) * W.φ m +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ m ^ 2)) := by
  have hω := W.two_mul_ψ_mul_ωP m
  rw [ψ₂_expl] at *
  simp only [map_ofNat] at *
  unfold addX WeierstrassCurve.toPoly WeierstrassCurve.map
  simp only [RingHom.comp_apply, Matrix.cons_val]
  linear_combination (norm := ring)
    -(2 * (Polynomial.X : R[X][X]) +
      Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
      Polynomial.C (Polynomial.C W.a₃)) * hω

-- mk(ψ_m) ≠ 0 for m ≠ 0 (needed for domain cancellation).
-- Strategy (following Torsion.lean): mk(ψ_m) = mk(Ψ_m), and Ψ_m ≠ 0 with natDegree < 2,
-- so mk_ne_zero_of_natDegree_lt applies. preΨ_m ≠ 0 from Mathlib's preΨ_ne_zero.
omit [Invertible (2 : R)] in
private lemma mk_ψ_ne_zero (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0)
    (m : ℤ) (hm : m ≠ 0) :
    AdjoinRoot.mk W.toAffine.polynomial (W.ψ m) ≠ 0 := by
  rw [Affine.CoordinateRing.mk_ψ]
  -- Goal: mk(Ψ m) ≠ 0
  -- ψ₂ ≠ 0 and has natDegree ≤ 1
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    have h2 := hψ_ne 2 (by omega)
    rwa [ψ_two] at h2
  have hψ₂_deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, Affine.polynomialY]; exact Polynomial.natDegree_linear_le
  -- Ψ m ≠ 0 (from preΨ_ne_zero, using hcast)
  have hΨ_ne : W.Ψ m ≠ 0 := by
    rw [WeierstrassCurve.Ψ]
    have hC : Polynomial.C (W.preΨ m) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (W.preΨ_ne_zero (hcast m hm))
    by_cases heven : Even m
    · simp only [heven, ↓reduceIte]; exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]; exact hC
  -- natDegree(Ψ m) < natDegree(polynomial) = 2
  have hΨ_deg : (W.Ψ m).natDegree < W.toAffine.polynomial.natDegree := by
    rw [Affine.natDegree_polynomial, WeierstrassCurve.Ψ]
    by_cases heven : Even m
    · simp only [heven, ↓reduceIte]
      calc (Polynomial.C (W.preΨ m) * W.ψ₂).natDegree
          ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
            (Nat.add_le_add (Polynomial.natDegree_C _).le hψ₂_deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have : (Polynomial.C (W.preΨ m)).natDegree = 0 := Polynomial.natDegree_C _
      omega
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt Affine.monic_polynomial hΨ_ne hΨ_deg

-- The ω-free expression is divisible by F_W.
set_option maxHeartbeats 800000000 in
set_option maxRecDepth 16000 in
private theorem ωfree_dvd (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0) (m : ℤ) :
    W.toAffine.polynomial ∣
      (Polynomial.C (Polynomial.C (2 : R)) *
        (addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ m, 0, W.ψ m]) -
         W.ψ (m - 1) ^ 2 * W.φ (m + 1)) -
       W.ψ 2 * (W.ψ (2 * m) - W.ψ m ^ 2 *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ m +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ m ^ 2))) := by
  -- Rewrite ψ 2 → ψ₂
  rw [ψ_two]
  -- Goal: F_W | E where E involves ψ₂
  -- Strategy: show mk(E) = 0 in the CR (coordinate ring = AdjoinRoot F_W, a domain).
  rw [← AdjoinRoot.mk_eq_zero]
  -- Suffices: mk(E) * mk(ψ_m)² = 0 (then cancel mk(ψ_m)² in the domain).
  -- From probe: mk(E * ψ_m²) = 0
  have h_probe := probe W hψ_ne m
  -- Convert: mk(E) * mk(ψ_m)² = mk(E * ψ_m²) = 0
  have h_prod : AdjoinRoot.mk W.toAffine.polynomial
      (Polynomial.C (Polynomial.C (2 : R)) *
        (addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ m, 0, W.ψ m]) -
         W.ψ (m - 1) ^ 2 * W.φ (m + 1)) -
       W.ψ₂ * (W.ψ (2 * m) - W.ψ m ^ 2 *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ m +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ m ^ 2))) *
    AdjoinRoot.mk W.toAffine.polynomial (W.ψ m) ^ 2 = 0 := by
    rw [← map_pow, ← map_mul]
    exact h_probe
  -- CR is a domain (F_W is irreducible → AdjoinRoot is a domain)
  haveI : IsDomain (AdjoinRoot W.toAffine.polynomial) := by
    exact inferInstance -- should be inferred from WeierstrassCurve.Affine.instIsDomainCoordinateRing
  -- Either mk(E) = 0 or mk(ψ_m)² = 0
  rcases mul_eq_zero.mp h_prod with h | h
  · exact h
  · -- mk(ψ_m)² = 0, so mk(ψ_m) = 0
    have hψm : AdjoinRoot.mk W.toAffine.polynomial (W.ψ m) = 0 := by
      exact pow_eq_zero_iff (n := 2) (by omega) |>.mp h
    -- For m = 0: ψ_0 = 0, so mk(ψ_0) = 0. Need to show mk(E) = 0 when ψ_m = 0.
    -- When ψ_m = 0: addX simplifies, ψ(2m) = ψ_0 = 0 (if m=0), etc.
    by_cases hm : m = 0
    · subst hm
      simp only [ψ_zero, ψ_one, ψ_neg, φ_zero, φ_one,
        show (2 : ℤ) * 0 = 0 from by ring,
        show (0 : ℤ) - 1 = -1 from by ring, show (0 : ℤ) + 1 = 1 from by ring]
      unfold addX WeierstrassCurve.toPoly WeierstrassCurve.map Affine.polynomial
      simp [RingHom.comp_apply, Matrix.cons_val, map_ofNat]
    · -- m ≠ 0: mk(ψ_m) = 0 contradicts mk_ψ_ne_zero
      exact absurd hψm (mk_ψ_ne_zero W hψ_ne hcast m hm)

/-- **ATOM 4a (general m).** X-component projective identity for ALL m.
In the coordinate ring R[W], the X-coordinate of the formal addition
P + [m]P equals ψ_{m-1}² · φ_{m+1}. -/
theorem mk_addX_divPoly_general (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0) (m : ℤ) :
    (AdjoinRoot.mk W.toAffine.polynomial)
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) -
       W.ψ (m - 1) ^ 2 * W.φ (m + 1)) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  have h := addX_elim_ω_gen W m
  have hd := ωfree_dvd W hψ_ne hcast m
  rw [← h] at hd
  exact (IsUnit.dvd_mul_left (by
    rw [Polynomial.isUnit_C, Polynomial.isUnit_C]
    exact isUnit_of_invertible 2)).mp hd

end GeneralM

#print axioms mk_addX_divPoly_general
