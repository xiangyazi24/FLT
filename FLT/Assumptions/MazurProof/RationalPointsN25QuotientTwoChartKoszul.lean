import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCharts
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoGradedKoszul
import Mathlib.Tactic

/-!
# Koszul complexes on the standard projective charts of the N25 curve

The homogeneous Koszul resolution belongs to the ambient projective space,
not to the quotient curve.  On `D₊(X i)` its two equations are the degree-zero
fractions `Q / X_i²` and `C / X_i³`.  This file constructs the resulting
affine Koszul complex over the ambient chart ring and identifies its cokernel
with the explicit quotient chart.

The proofs deliberately retain the two equations as structural generators.
In particular, exactness at the right-hand ambient module follows from the
previously proved kernel theorem, rather than from coordinate expansion on
the four individual charts.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoChartKoszul

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoConormal
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-zero homogeneous localization for the ambient chart
`D₊(X i) ⊆ ℙ³`. -/
abbrev AmbientChartRing (i : Fin 4) := StandardChart i

/-- The left chart Koszul differential sends `r` to
`((C / X_i³)r, -(Q / X_i²)r)`. -/
def chartKoszulTop (i : Fin 4) :
    AmbientChartRing i →ₗ[AmbientChartRing i]
      AmbientChartRing i × AmbientChartRing i :=
  (LinearMap.lsmul (AmbientChartRing i) (AmbientChartRing i)
      (dehomogenizedCubic i)).prod
    (-(LinearMap.lsmul (AmbientChartRing i) (AmbientChartRing i)
      (dehomogenizedQuadric i)))

/-- The middle chart Koszul differential sends `(a,b)` to
`(Q / X_i²)a + (C / X_i³)b`. -/
def chartKoszulMiddle (i : Fin 4) :
    AmbientChartRing i × AmbientChartRing i →ₗ[AmbientChartRing i]
      AmbientChartRing i :=
  (LinearMap.lsmul (AmbientChartRing i) (AmbientChartRing i)
      (dehomogenizedQuadric i)).coprod
    (LinearMap.lsmul (AmbientChartRing i) (AmbientChartRing i)
      (dehomogenizedCubic i))

/-- The right chart differential is the quotient by the two dehomogenized
equations. -/
def chartQuotientProjection (i : Fin 4) :
    AmbientChartRing i →ₗ[AmbientChartRing i]
      AmbientChartRing i ⧸ chartEquationIdeal i :=
  (Ideal.Quotient.mkₐ (AmbientChartRing i) (chartEquationIdeal i)).toLinearMap

/-- Coordinate formula for the left chart Koszul differential. -/
@[simp]
theorem chartKoszulTop_apply (i : Fin 4) (r : AmbientChartRing i) :
    chartKoszulTop i r =
      (dehomogenizedCubic i * r, -(dehomogenizedQuadric i * r)) := by
  rfl

/-- Coordinate formula for the middle chart Koszul differential. -/
@[simp]
theorem chartKoszulMiddle_apply (i : Fin 4)
    (p : AmbientChartRing i × AmbientChartRing i) :
    chartKoszulMiddle i p =
      dehomogenizedQuadric i * p.1 + dehomogenizedCubic i * p.2 := by
  rfl

/-- Coordinate formula for the quotient differential. -/
@[simp]
theorem chartQuotientProjection_apply (i : Fin 4) (r : AmbientChartRing i) :
    chartQuotientProjection i r = Ideal.Quotient.mk (chartEquationIdeal i) r := by
  rfl

/-- The two chart Koszul differentials compose to zero. -/
theorem chartKoszulMiddle_comp_top (i : Fin 4) :
    (chartKoszulMiddle i).comp (chartKoszulTop i) = 0 := by
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, chartKoszulMiddle_apply,
    chartKoszulTop_apply, LinearMap.zero_apply]
  ring

/-- Exactness at the middle free module on every standard chart.

The proof does not expand the four charts.  Write both degree-zero fractions
with homogeneous numerators, put their two denominators over a common power
of `X_i`, and cancel the remaining localization denominator in the ambient
polynomial domain.  The resulting homogeneous syzygy has total degree
`n + m + 5`, so the already proved degreewise Koszul exactness supplies a
homogeneous witness of degree `n + m`.  Dividing that witness by
`X_i^(n+m)` returns the required degree-zero chart element. -/
theorem chartKoszul_exact_top_middle (i : Fin 4) :
    Function.Exact (chartKoszulTop i) (chartKoszulMiddle i) := by
  intro p
  constructor
  · intro hp
    rcases p with ⟨x, y⟩
    obtain ⟨n, a, ha, hxa⟩ :=
      Away.mk_surjective standardConePiece (coordinate_isHomogeneous i) x
    obtain ⟨m, b, hb, hyb⟩ :=
      Away.mk_surjective standardConePiece (coordinate_isHomogeneous i) y
    rw [← hxa, ← hyb] at hp
    have hpval := congrArg HomogeneousLocalization.val hp
    simp only [chartKoszulMiddle_apply, HomogeneousLocalization.val_add,
      HomogeneousLocalization.val_mul, dehomogenizedQuadric,
      dehomogenizedCubic, Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_mul, Localization.add_mk] at hpval
    rw [Localization.mk_eq_mk'_apply,
      IsLocalization.mk'_eq_zero_iff] at hpval
    obtain ⟨t, ht⟩ := hpval
    obtain ⟨l, hl⟩ := t.property
    have htne : (t : S) ≠ 0 := by
      rw [← hl]
      exact pow_ne_zero l (MvPolynomial.X_ne_zero i)
    have hnum := (mul_eq_zero.mp ht).resolve_left htne
    have hnum' :
        MvPolynomial.X i ^ (2 + n) *
            (canonicalCubicPolynomial25Two * b) +
          MvPolynomial.X i ^ (3 + m) *
            (canonicalQuadricPolynomial25Two * a) = 0 := by
      simpa only [Submonoid.coe_mul, Subtype.coe_mk, pow_add] using hnum
    have hrelation :
        canonicalQuadricPolynomial25Two *
            (a * MvPolynomial.X i ^ (m + 3)) +
          canonicalCubicPolynomial25Two *
            (b * MvPolynomial.X i ^ (n + 2)) = 0 := by
      linear_combination hnum'
    let N := n + m + 5
    let aa : shiftedPiece 2 N :=
      ⟨a * MvPolynomial.X i ^ (m + 3), by
        rw [shiftedPiece, if_pos (by omega : 2 ≤ N)]
        change (a * MvPolynomial.X i ^ (m + 3)).IsHomogeneous (N - 2)
        have haHom : a.IsHomogeneous n := by simpa using ha
        have hprod :=
          haHom.mul (MvPolynomial.isHomogeneous_X_pow i (m + 3))
        convert hprod using 1 <;> omega⟩
    let bb : shiftedPiece 3 N :=
      ⟨b * MvPolynomial.X i ^ (n + 2), by
        rw [shiftedPiece, if_pos (by omega : 3 ≤ N)]
        change (b * MvPolynomial.X i ^ (n + 2)).IsHomogeneous (N - 3)
        have hbHom : b.IsHomogeneous m := by simpa using hb
        have hprod :=
          hbHom.mul (MvPolynomial.isHomogeneous_X_pow i (n + 2))
        convert hprod using 1 <;> omega⟩
    have hmiddle : gradedKoszulMiddle N (aa, bb) = 0 := by
      apply Subtype.ext
      simpa only [gradedKoszulMiddle_coe, Submodule.coe_zero, aa, bb] using
        hrelation
    obtain ⟨w, hw⟩ :=
      (gradedKoszul_exact_top_middle N (aa, bb)).mp hmiddle
    have hwfst :
        canonicalCubicPolynomial25Two * (w : S) =
          a * MvPolynomial.X i ^ (m + 3) := by
      simpa only [gradedKoszulTop_fst_coe, aa] using
        congrArg (fun q ↦ ((q.1 : shiftedPiece 2 N) : S)) hw
    have hwsnd :
        -(canonicalQuadricPolynomial25Two * (w : S)) =
          b * MvPolynomial.X i ^ (n + 2) := by
      simpa only [gradedKoszulTop_snd_coe, bb] using
        congrArg (fun q ↦ ((q.2 : shiftedPiece 3 N) : S)) hw
    have hwHom : (w : S).IsHomogeneous (n + m) := by
      simpa [N] using shiftedPiece_isHomogeneous w
    let z : AmbientChartRing i :=
      Away.mk standardConePiece (coordinate_isHomogeneous i) (n + m) (w : S)
        (by simpa using hwHom)
    refine ⟨z, ?_⟩
    rw [← hxa, ← hyb]
    apply Prod.ext
    · apply HomogeneousLocalization.val_injective
      simp only [chartKoszulTop_apply, HomogeneousLocalization.val_mul,
        dehomogenizedCubic, Away.val_mk, z, Localization.mk_mul]
      rw [hwfst, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
      simp only [pow_add]
      ring
    · apply HomogeneousLocalization.val_injective
      simp only [chartKoszulTop_apply, HomogeneousLocalization.val_neg,
        HomogeneousLocalization.val_mul, dehomogenizedQuadric, Away.val_mk,
        z, Localization.mk_mul, Localization.neg_mk]
      rw [hwsnd, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
      simp only [pow_add]
      ring
  · rintro ⟨r, rfl⟩
    simp only [chartKoszulMiddle_apply, chartKoszulTop_apply]
    ring

/-- The image of the middle chart differential is precisely the explicit
two-equation ideal. -/
theorem chartKoszulMiddle_range_eq_equationIdeal (i : Fin 4) :
    LinearMap.range (chartKoszulMiddle i) = chartEquationIdeal i := by
  ext r
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [chartEquationIdeal, Ideal.mem_span_pair]
    exact ⟨a, b, by simp only [chartKoszulMiddle_apply]; ring⟩
  · intro hr
    rw [chartEquationIdeal, Ideal.mem_span_pair] at hr
    obtain ⟨a, b, hab⟩ := hr
    exact ⟨(a, b), by simpa only [chartKoszulMiddle_apply, mul_comm] using hab⟩

/-- Exactness at the right-hand ambient module identifies the cokernel of
the local Koszul differential with the coordinate ring of the curve chart. -/
theorem chartKoszul_exact_middle_projection (i : Fin 4) :
    Function.Exact (chartKoszulMiddle i) (chartQuotientProjection i) := by
  rw [LinearMap.exact_iff]
  rw [show LinearMap.ker (chartQuotientProjection i) = chartEquationIdeal i by
    change RingHom.ker (Ideal.Quotient.mk (chartEquationIdeal i)) = _
    exact Ideal.mk_ker]
  exact (chartKoszulMiddle_range_eq_equationIdeal i).symm

/-- The local quotient differential is surjective. -/
theorem chartQuotientProjection_surjective (i : Fin 4) :
    Function.Surjective (chartQuotientProjection i) :=
  Ideal.Quotient.mk_surjective

end MazurProof.RationalPointsN25QuotientTwoChartKoszul
