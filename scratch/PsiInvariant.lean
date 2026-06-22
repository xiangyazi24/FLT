import scratch.WardInvariant
import scratch.PsiSomos
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open Polynomial
open scoped Polynomial
open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

private def preΨInvN (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  W.preΨ (m + 2) * W.preΨ (m - 1)^2
    + W.preΨ (m + 1)^2 * W.preΨ (m - 2)
    + (if Even m then W.Ψ₂Sq^2 else 1) * W.preΨ m^3

private def preΨInvD (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)

private lemma preΨ_invariant_even
    [IsDomain R]
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : Even m) :
    W.Ψ₃ * preΨInvN W m
      = (W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m := by
  classical

  let mkC : R[X] →+* _ := (Affine.CoordinateRing.mk W).comp Polynomial.C
  let q : _ := Affine.CoordinateRing.mk W W.ψ₂

  have hmkC : Function.Injective mkC := by
    -- Replace this line by your exact local lemma if namespaced differently.
    simpa [mkC, Function.comp_def] using (mk_C_injective (W := W))

  have hs_ne : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero (W := W) h4

  have hq2 : q^2 = mkC W.Ψ₂Sq := by
    simpa [q, mkC, sq] using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))

  have hmkCs_ne : mkC W.Ψ₂Sq ≠ 0 := by
    intro h
    apply hs_ne
    apply hmkC
    simpa [mkC] using h

  have hq2_ne : q^2 ≠ 0 := by
    simpa [hq2] using hmkCs_ne

  have hq_ne : q ≠ 0 := by
    intro hq
    apply hq2_ne
    simp [hq]

  have hq4 : q^4 = mkC (W.Ψ₂Sq^2) := by
    calc
      q^4 = (q^2)^2 := by ring
      _ = (mkC W.Ψ₂Sq)^2 := by rw [hq2]
      _ = mkC (W.Ψ₂Sq^2) := by simp [mkC]

  have hne_norm :
      ∀ k : ℤ, k ≠ 0 → normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) k ≠ 0 := by
    intro k hk
    simpa [WeierstrassCurve.ψ] using hψ_ne k hk

  have hWard :=
    invarRel_all
      (R := Polynomial (Polynomial R))
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      hne_norm m

  have hWardψ :
      C W.Ψ₃ *
          (W.ψ (m + 2) * W.ψ (m - 1)^2
            + W.ψ (m + 1)^2 * W.ψ (m - 2)
            + W.ψ₂^2 * W.ψ m^3)
        = (C W.preΨ₄ + W.ψ₂^4)
          * (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1)) := by
    simpa [InvarRel, Nseq, Dseq, WeierstrassCurve.ψ] using hWard

  have hMk := congrArg (Affine.CoordinateRing.mk W) hWardψ

  have hm_p2 : Even (m + 2) := by simp [parity_simps, hm]
  have hm_m2 : Even (m - 2) := by simp [parity_simps, hm]
  have hm_p1 : ¬ Even (m + 1) := by simp [parity_simps, hm]
  have hm_m1 : ¬ Even (m - 1) := by simp [parity_simps, hm]

  -- ψ-to-preΨ parity normalization.  In this even branch both Nseq and Dseq
  -- carry exactly one factor `q = mk ψ₂`.
  have hq_mul :
      q * mkC (W.Ψ₃ * preΨInvN W m)
        = q * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    sorry  -- KEYSTONE_INV_NORM: coord-ring ψ→preΨ normalization (CAS-verified statement)

  have hmk_eq :
      mkC (W.Ψ₃ * preΨInvN W m)
        = mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) :=
    mul_left_cancel₀ hq_ne hq_mul

  exact hmkC hmk_eq

private lemma preΨ_invariant_odd
    [IsDomain R]
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : ¬ Even m) :
    W.Ψ₃ * preΨInvN W m
      = (W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m := by
  classical

  let mkC : R[X] →+* _ := (Affine.CoordinateRing.mk W).comp Polynomial.C
  let q : _ := Affine.CoordinateRing.mk W W.ψ₂

  have hmkC : Function.Injective mkC := by
    -- Replace this line by your exact local lemma if namespaced differently.
    simpa [mkC, Function.comp_def] using (mk_C_injective (W := W))

  have hs_ne : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero (W := W) h4

  have hq2 : q^2 = mkC W.Ψ₂Sq := by
    simpa [q, mkC, sq] using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))

  have hmkCs_ne : mkC W.Ψ₂Sq ≠ 0 := by
    intro h
    apply hs_ne
    apply hmkC
    simpa [mkC] using h

  have hq2_ne : q^2 ≠ 0 := by
    simpa [hq2] using hmkCs_ne

  have hq4 : q^4 = mkC (W.Ψ₂Sq^2) := by
    calc
      q^4 = (q^2)^2 := by ring
      _ = (mkC W.Ψ₂Sq)^2 := by rw [hq2]
      _ = mkC (W.Ψ₂Sq^2) := by simp [mkC]

  have hne_norm :
      ∀ k : ℤ, k ≠ 0 → normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) k ≠ 0 := by
    intro k hk
    simpa [WeierstrassCurve.ψ] using hψ_ne k hk

  have hWard :=
    invarRel_all
      (R := Polynomial (Polynomial R))
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      hne_norm m

  have hWardψ :
      C W.Ψ₃ *
          (W.ψ (m + 2) * W.ψ (m - 1)^2
            + W.ψ (m + 1)^2 * W.ψ (m - 2)
            + W.ψ₂^2 * W.ψ m^3)
        = (C W.preΨ₄ + W.ψ₂^4)
          * (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1)) := by
    simpa [InvarRel, Nseq, Dseq, WeierstrassCurve.ψ] using hWard

  have hMk := congrArg (Affine.CoordinateRing.mk W) hWardψ

  have hm_p2 : ¬ Even (m + 2) := by simp [parity_simps, hm]
  have hm_m2 : ¬ Even (m - 2) := by simp [parity_simps, hm]
  have hm_p1 : Even (m + 1) := by rw [Int.even_add_one]; exact hm
  have hm_m1 : Even (m - 1) := by rw [Int.even_sub_one]; exact hm

  -- ψ-to-preΨ parity normalization.  In this odd branch both Nseq and Dseq
  -- carry exactly `q^2 = mkC Ψ₂Sq`.
  have hq2_mul :
      q^2 * mkC (W.Ψ₃ * preΨInvN W m)
        = q^2 * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    sorry  -- KEYSTONE_INV_NORM: coord-ring ψ→preΨ normalization (CAS-verified statement)

  have hmk_eq :
      mkC (W.Ψ₃ * preΨInvN W m)
        = mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) :=
    mul_left_cancel₀ hq2_ne hq2_mul

  exact hmkC hmk_eq

/-- The invariant relation for the univariate auxiliary division-polynomial sequence `preΨ`.

This is Ward's invariant for the bivariate division-polynomial EDS `ψ`, descended through the
affine coordinate ring.  The only cancellation is by `mk ψ₂` in the even case and by
`mk ψ₂ ^ 2` in the odd case; both are justified by `mk_ψ₂_sq` and `Ψ₂Sq_ne_zero h4`.
-/
lemma preΨ_invariant
    [IsDomain R]
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (m : ℤ) :
    W.Ψ₃ *
        (W.preΨ (m + 2) * W.preΨ (m - 1)^2
          + W.preΨ (m + 1)^2 * W.preΨ (m - 2)
          + (if Even m then W.Ψ₂Sq^2 else 1) * W.preΨ m^3)
      = (W.preΨ₄ + W.Ψ₂Sq^2)
          * (W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)) := by
  by_cases hm : Even m
  · simpa [preΨInvN, preΨInvD, hm] using
      preΨ_invariant_even (W := W) h4 hψ_ne (m := m) hm
  · simpa [preΨInvN, preΨInvD, hm] using
      preΨ_invariant_odd (W := W) h4 hψ_ne (m := m) hm

end

end WeierstrassCurve
