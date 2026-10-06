import FLT.Assumptions.MazurProof.N25F_SharpBasis
import FLT.Assumptions.MazurProof.N25F_NoQuadraticPoints

/-!
# Four sections of the canonical boundary divisor

Let `H = 3 X + YZ + 2 Z`, a boundary divisor of degree six.  At the boundary
points the W-chart coordinates have the orders

* at `X`: `x ↦ -3`, `y ↦ -2`, `z ↦ -1`;
* at `YZ`: `y, z ↦ -1`, `x ≥ -1`;
* at `Z`: `z ↦ -2`, `x, y ≥ -2`,

and they are regular on the affine chart, so `1, x, y, z ∈ L(H)`.  They are
linearly independent over `F₂`: with `x = b₂ - z b₁` an `F₂`-relation
`c₀ + c₁ x + c₂ y + c₃ z = 0` becomes the `F₂[z]`-relation
`(c₀ + c₃ z) b₀ + (c₂ - c₁ z) b₁ + c₁ b₂ = 0` among the sharp family of
`N25F_SharpBasis`, which forces every `cᵢ = 0`.  Hence `ℓ(H) ≥ 4`, and for every
effective `E` of degree two, `ℓ(H - E) ≥ 2` by `N25F_NoQuadraticPoints`.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_CanonicalSections

open Polynomial WithZero
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneQuarticSeparable
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoWChartNormalization
open N25F_NonBoundaryPrincipalDivisor
open N25F_XChartFractionMap N25F_XLocalFractionEmbedding N25F_XLocalDVR
open N25F_XCoordinateOrders N25F_XBoundaryOrder N25F_XBoundaryZOrder
open N25F_YZLocalFractionEmbedding N25F_YZLocalDVR N25F_YZBoundaryOrder N25F_YZOverlapMap
open N25F_ZChartFractionMap N25F_ZChartWChartEquiv N25F_ZBoundaryOrder
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_RiemannRochSpace N25F_WBasisPoleSections N25F_ZeroDegreeConstants

open N25F_SharpBasis N25F_WBasisPoleSections
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_NoQuadraticPoints

local notation "P" => Polynomial (ZMod 2)
local notation "K" => FractionRing W
local notation "F" => algebraMap W K
local notation "Ox" => xLocalFractionOrder
local notation "Oyz" => yzLocalFractionOrder
local notation "Oz" => zLocalFractionOrder

/-- The boundary divisor `3 X + YZ + 2 Z` of degree six. -/
def canonicalDivisor25Two : ProjectiveDivisor25Two :=
  Finsupp.single (fullBoundaryAtomOfTag .X) 3 +
    Finsupp.single (fullBoundaryAtomOfTag .YZ) 1 +
      Finsupp.single (fullBoundaryAtomOfTag .Z) 2

theorem canonicalDivisor25Two_degree :
    fullClosedPointGrading25Two.divisorDegree canonicalDivisor25Two = 6 := by
  unfold canonicalDivisor25Two
  rw [map_add, map_add]
  simp [ClosedPointGrading.divisorDegree]

private theorem canonical_apply_boundary (t : FullBoundaryTag25Two) :
    canonicalDivisor25Two (fullBoundaryAtomOfTag t) =
      match t with | .X => 3 | .YZ => 1 | .Z => 2 := by
  cases t <;> simp [canonicalDivisor25Two, fullBoundaryAtomOfTag_injective.eq_iff]

private theorem canonical_apply_nonBoundary (A : FullNonBoundaryAtom25Two) :
    canonicalDivisor25Two A.1 = 0 := by
  have hn (t : FullBoundaryTag25Two) : fullBoundaryAtomOfTag t ≠ A.1 := by
    intro h
    exact A.2 (h ▸ fullBoundaryAtomOfTag_isFullBoundaryAtom t)
  simp [canonicalDivisor25Two, Ne.symm (hn .X), Ne.symm (hn .YZ), Ne.symm (hn .Z)]

/-- A regular W-chart function with poles at most `3, 1, 2` at `X, YZ, Z`
lies in `L(H)`. -/
theorem regular_function_mem_canonical (a : W) (ha : a ≠ 0)
    (f : Additive Kˣ) (hf : (f.toMul : K) = algebraMap W K a)
    (hx : -3 ≤ xBoundaryOrder f) (hyz : -1 ≤ yzBoundaryOrder f)
    (hz : -2 ≤ zBoundaryOrder f) :
    (f.toMul : K) ∈ fullRiemannRochSpace25Two canonicalDivisor25Two := by
  classical
  refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
  have hunit : Additive.ofMul (Units.mk0 (f.toMul : K) f.toMul.ne_zero) = f := by
    apply Additive.toMul.injective
    exact Units.ext rfl
  intro A
  rw [hunit]
  by_cases hA : IsFullBoundaryAtom A
  · obtain ⟨t, rfl⟩ := (isFullBoundaryAtom_iff_exists_fullBoundaryTag A).mp hA
    rw [canonical_apply_boundary]
    cases t with
    | X =>
        rw [projectivePrincipalDivisor_apply_X]; change 0 ≤ 3 + xBoundaryOrder f; omega
    | YZ =>
        rw [projectivePrincipalDivisor_apply_YZ]; change 0 ≤ 1 + yzBoundaryOrder f; omega
    | Z =>
        rw [projectivePrincipalDivisor_apply_Z]; change 0 ≤ 2 + zBoundaryOrder f; omega
  · let B : FullNonBoundaryAtom25Two := ⟨A, hA⟩
    have hb : canonicalDivisor25Two A = 0 := canonical_apply_nonBoundary B
    rw [hb, zero_add]
    rw [projectivePrincipalDivisor_apply_nonBoundary f B, nonBoundaryPrincipalDivisor_apply,
      CurveDedekindDivisor.principalDivisor_regular_apply a ha f hf]
    exact Int.natCast_nonneg _

/-- The pole-bound form of `regular_function_mem_canonical`. -/
theorem mem_canonical_of_poleLE (a : W) (hne : F a ≠ 0)
    (hx : PoleLE Ox (F a) 3) (hyz : PoleLE Oyz (F a) 1) (hz : PoleLE Oz (F a) 2) :
    F a ∈ fullRiemannRochSpace25Two canonicalDivisor25Two :=
  regular_function_mem_canonical a (fun h => hne (by rw [h, map_zero]))
    (Additive.ofMul (Units.mk0 _ hne)) rfl
    (neg_le_log_of_poleLE hne hx) (neg_le_log_of_poleLE hne hyz) (neg_le_log_of_poleLE hne hz)

/-- The four sections `1, x, y, z`. -/
def canonicalFamily : Fin 4 → W := ![1, qx, qy, qz]

theorem canonicalFamily_mem (i : Fin 4) :
    F (canonicalFamily i) ∈ fullRiemannRochSpace25Two canonicalDivisor25Two := by
  fin_cases i
  · exact mem_canonical_of_poleLE 1 (by simp) (by simpa using poleLE_one.mono (by norm_num))
      (by simpa using poleLE_one.mono (by norm_num))
      (by simpa using poleLE_one.mono (by norm_num))
  · exact mem_canonical_of_poleLE qx fraction_qx_ne_zero (poleLE_of_eq x_qx) yz_qx z_qx
  · exact mem_canonical_of_poleLE qy fraction_qy_ne_zero
      ((poleLE_of_eq x_qy).mono (by norm_num)) (poleLE_of_eq yz_qy) z_qy
  · exact mem_canonical_of_poleLE qz fraction_qz_ne_zero
      ((poleLE_of_eq x_qz).mono (by norm_num)) (poleLE_of_eq yz_qz) (poleLE_of_eq z_qz)

private theorem zmod_smul_eq (c : ZMod 2) (w : W) :
    c • F w = F (algebraMap P W (Polynomial.C c) * w) := by
  have hv := ZMod.val_lt c
  have h : c = 0 ∨ c = 1 := by
    have : c.val = 0 ∨ c.val = 1 := by omega
    rcases this with h | h
    · left; apply ZMod.val_injective 2; simpa using h
    · right; apply ZMod.val_injective 2; simpa only [ZMod.val_one_eq_one_mod] using h
  rcases h with rfl | rfl <;> simp

/-- `1, x, y, z` are linearly independent over `F₂`. -/
theorem canonicalFamily_linearIndependent :
    LinearIndependent (ZMod 2) (fun i => F (canonicalFamily i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_four, zmod_smul_eq, ← map_add] at hc
  have hW : algebraMap P W (Polynomial.C (c 0)) * canonicalFamily 0 +
      algebraMap P W (Polynomial.C (c 1)) * canonicalFamily 1 +
      algebraMap P W (Polynomial.C (c 2)) * canonicalFamily 2 +
      algebraMap P W (Polynomial.C (c 3)) * canonicalFamily 3 = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective W K)).mp hc
  have hz : algebraMap P W X = qz := algebraMap_Rz_X
  let g : Fin 4 → P := ![Polynomial.C (c 0) + Polynomial.C (c 3) * X,
    Polynomial.C (c 2) - Polynomial.C (c 1) * X, Polynomial.C (c 1), 0]
  have hg := Fintype.linearIndependent_iff.mp sharpBasis_linearIndependent g (by
    simp only [Fin.sum_univ_four, Algebra.smul_def, g, sharpBasis, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, map_add, map_sub,
      map_mul, map_zero, hz, Matrix.head_cons, Matrix.tail_cons]
    simp only [canonicalFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hW
    linear_combination hW)
  have e1 : c 1 = 0 := Polynomial.C_eq_zero.mp (hg 2)
  have e2 : c 2 = 0 := by
    have h := hg 1
    simp only [g, Matrix.cons_val_one, e1, map_zero, zero_mul,
      sub_zero] at h
    exact Polynomial.C_eq_zero.mp h
  have h0 := hg 0
  simp only [g, Matrix.cons_val_zero] at h0
  have e0 : c 0 = 0 := by
    simpa using congrArg (fun p : P => p.coeff 0) h0
  have e3 : c 3 = 0 := by
    simpa using congrArg (fun p : P => p.coeff 1) h0
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

/-- `ℓ(H) ≥ 4`. -/
theorem four_le_finrank_canonical :
    4 ≤ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two canonicalDivisor25Two) := by
  let v : Fin 4 → fullRiemannRochSpace25Two canonicalDivisor25Two :=
    fun i => ⟨_, canonicalFamily_mem i⟩
  have hv : LinearIndependent (ZMod 2) v :=
    LinearIndependent.of_comp (fullRiemannRochSpace25Two canonicalDivisor25Two).subtype
      canonicalFamily_linearIndependent
  simpa using hv.fintype_card_le_finrank

/-- For every effective divisor `E` of degree two, `ℓ(H - E) ≥ 2`. -/
theorem two_le_finrank_canonical_sub (E : ProjectiveDivisor25Two) (hE : ∀ A, 0 ≤ E A)
    (hdeg : fullClosedPointGrading25Two.divisorDegree E = 2) :
    2 ≤ Module.finrank (ZMod 2)
      (fullRiemannRochSpace25Two (canonicalDivisor25Two - E)) := by
  have h := finrank_le_sub_add_degree canonicalDivisor25Two 2 E hE (by exact_mod_cast hdeg)
    le_rfl
  have h4 := four_le_finrank_canonical
  omega

end MazurProof.N25F_CanonicalSections
