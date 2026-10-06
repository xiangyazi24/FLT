import FLT.Assumptions.MazurProof.N25F_OrderCalculus

/-!
# Local data at the five rational points of the N25 curve

The five `F₂`-rational points of the N25 quotient curve, with coordinates
`[x:y:z:w]`, are

* `X = [1:0:0:0]`, `YZ = [0:1:1:0]` and `Z = [0:0:1:0]` on the boundary `w = 0`;
* `R = [0:0:0:1]` and `P = [1:1:0:1]` on the affine chart `w = 1`.

At the boundary points we record the known orders of the affine coordinates
`qx = x/w`, `qy = y/w` and `qz = z/w`.  At `Z` we also need `ord_Z (qy/qz) ≥ 1`,
which holds because the chart coordinate `y/z` vanishes at `Z`.  Every regular
function on the chart `w = 1` is integral at the nonboundary points, and it
vanishes at `R` or `P` when its value there is zero.

`lof cX cYZ cZ cR cP` is the divisor `cX·X + cYZ·YZ + cZ·Z + cR·R + cP·P`.
`div_eq_lof` turns lower bounds at the five points, plus regularity elsewhere
on the chart, into an exact divisor whenever the coefficients sum to zero.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_RationalPointOrders
open Polynomial
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoClosedPointEvaluation
open RationalPointsN25QuotientTwoHyperplaneArtin
open RationalPointsN25QuotientTwoCanonicalDivisor
open RationalPointsN25QuotientTwoConormal RationalPointsN25QuotientWeil
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_PrincipalOrderAddition
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorDegree
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap N25F_ZChartWChartEquiv
open N25F_SharpBasis N25F_XChartFractionInjective N25F_XChartFractionMap
open N25F_OrderCalculus
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local notation "F" => algebraMap N25F_NonBoundaryPrincipalDivisor.W K

local instance : zPrime.IsMaximal := zPrime_isMaximal
local instance : zPrime.IsPrime := zPrime_isMaximal.isPrime

/-! ## Two facts about a discrete valuation ring -/

private theorem dvr_nonneg {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] (a : R) (ha : a ≠ 0) :
    0 ≤ WithZero.log (Ring.ordFrac R (algebraMap R K a)) := by
  have hsL : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  have hv0 : Ring.ordFrac R (algebraMap R K a) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hsL).map (Ring.ordFrac R)).ne_zero
  simpa only [WithZero.log_one] using
    (WithZero.log_le_log (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 from one_ne_zero) hv0).mpr
      (Ring.ordFrac_ge_one_of_ne_zero ha)

private theorem dvr_pos {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] (a : R) (ha : a ≠ 0)
    (hm : a ∈ IsLocalRing.maximalIdeal R) :
    1 ≤ WithZero.log (Ring.ordFrac R (algebraMap R K a)) := by
  have hnot : ¬ IsUnit a := (IsLocalRing.mem_maximalIdeal _).mp hm
  have hsL : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  have hv0 : Ring.ordFrac R (algebraMap R K a) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hsL).map (Ring.ordFrac R)).ne_zero
  have hv1 : Ring.ordFrac R (algebraMap R K a) ≠ 1 := fun h1 =>
    hnot (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr h1)
  have hpos : 1 < Ring.ordFrac R (algebraMap R K a) :=
    lt_of_le_of_ne (Ring.ordFrac_ge_one_of_ne_zero ha) (Ne.symm hv1)
  have h := (WithZero.log_lt_log (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 from one_ne_zero)
    hv0).mpr hpos
  rw [WithZero.log_one] at h
  omega

/-! ## The boundary points -/

/-- The boundary point `X = [1:0:0:0]`. -/
def atomX : fullClosedPointGrading25Two.Atom := boundaryNonBoundaryToFullAtom (Sum.inl .X)
/-- The boundary point `YZ = [0:1:1:0]`. -/
def atomYZ : fullClosedPointGrading25Two.Atom := boundaryNonBoundaryToFullAtom (Sum.inl .YZ)
/-- The boundary point `Z = [0:0:1:0]`. -/
def atomZ : fullClosedPointGrading25Two.Atom := boundaryNonBoundaryToFullAtom (Sum.inl .Z)

theorem ordAt_atomX {f : K} (hf : f ≠ 0) :
    ordAt atomX f = WithZero.log (xLocalFractionOrder f) := by
  rw [ordAt_of_ne _ hf]
  simp only [atomX, boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_X]
  rfl

theorem ordAt_atomYZ {f : K} (hf : f ≠ 0) :
    ordAt atomYZ f = WithZero.log (yzLocalFractionOrder f) := by
  rw [ordAt_of_ne _ hf]
  simp only [atomYZ, boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_YZ]
  rfl

theorem ordAt_atomZ {f : K} (hf : f ≠ 0) :
    ordAt atomZ f = WithZero.log (zLocalFractionOrder f) := by
  rw [ordAt_of_ne _ hf]
  simp only [atomZ, boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_Z]
  rfl

theorem atomX_qx : ordAt atomX (F qx) = -3 := by
  rw [ordAt_atomX fraction_qx_ne_zero, x_qx, WithZero.log_exp]

theorem atomX_qy : ordAt atomX (F qy) = -2 := by
  rw [ordAt_atomX fraction_qy_ne_zero, x_qy, WithZero.log_exp]

theorem atomX_qz : ordAt atomX (F qz) = -1 := by
  rw [ordAt_atomX fraction_qz_ne_zero, x_qz, WithZero.log_exp]

theorem atomYZ_qy : ordAt atomYZ (F qy) = -1 := by
  rw [ordAt_atomYZ fraction_qy_ne_zero, yz_qy, WithZero.log_exp]

theorem atomYZ_qz : ordAt atomYZ (F qz) = -1 := by
  rw [ordAt_atomYZ fraction_qz_ne_zero, yz_qz, WithZero.log_exp]

theorem atomYZ_qx : Ge atomYZ (F qx) (-1) := by
  right
  rw [ordAt_atomYZ fraction_qx_ne_zero]
  exact neg_le_log_of_poleLE fraction_qx_ne_zero yz_qx

theorem atomZ_qz : ordAt atomZ (F qz) = -2 := by
  rw [ordAt_atomZ fraction_qz_ne_zero, z_qz, WithZero.log_exp]

/-- At `Z` the chart coordinate `x/z` is integral. -/
theorem atomZ_x : Ge atomZ (F qx / F qz) 0 := by
  have himg : zLocalToFraction (algebraMap ZChartRing ZLocalRing zX) = F qx / F qz := by
    rw [zLocalToFraction_algebraMap, zChartToFraction_zX]
  have hne : F qx / F qz ≠ 0 := div_ne_zero fraction_qx_ne_zero fraction_qz_ne_zero
  right
  rw [ordAt_atomZ hne]
  have h := neg_le_log_of_poleLE (by rw [himg]; exact hne)
    (z_integral (algebraMap ZChartRing ZLocalRing zX))
  rw [himg, neg_zero] at h
  exact h

/-- The chart coordinate `y/z` vanishes at `Z = [0:0:1:0]`. -/
private theorem zY_mem_zPrime : zY ∈ zPrime := by
  rw [zPrime, RingHom.mem_ker]
  change zPointEval zY = 0
  rw [zPointEval, zY, chartMap]
  change chartPointAffineEval 2
    (⟨hyperplanePointZ, rfl⟩ : CurvePointOnChart (2 : Fin 4) (ZMod 2))
    (ambientDehomogenize 2 (MvPolynomial.X 1)) = 0
  simp [ambientDehomogenize, dehomogenizedVariable, chartPointAffineEval,
    hyperplanePointZ, coordinates4ToFun,
    normalizedCoordinates25, NormalizedProjective4.coordinates,
    fieldBinaryOperations]

/-- At `Z` the chart coordinate `y/z` vanishes. -/
theorem atomZ_y : Ge atomZ (F qy / F qz) 1 := by
  have himg : zLocalToFraction (algebraMap ZChartRing ZLocalRing zY) = F qy / F qz := by
    rw [zLocalToFraction_algebraMap, zChartToFraction_zY]
  have hne : F qy / F qz ≠ 0 := div_ne_zero fraction_qy_ne_zero fraction_qz_ne_zero
  have ha : algebraMap ZChartRing ZLocalRing zY ≠ 0 := by
    intro h
    rw [h, map_zero] at himg
    exact hne himg.symm
  have hm : algebraMap ZChartRing ZLocalRing zY ∈ IsLocalRing.maximalIdeal ZLocalRing :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff ZLocalRing zPrime zY).mpr zY_mem_zPrime
  right
  rw [ordAt_atomZ hne, ← himg]
  letI : Algebra ZLocalRing K := zLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := zLocalToFraction_isFractionRing
  exact dvr_pos (algebraMap ZChartRing ZLocalRing zY) ha hm

/-! ## The affine chart -/

/-- Every regular function is integral at a nonboundary point, and vanishes
there when it lies in the corresponding prime. -/
theorem ge_nonBoundary (B : FullNonBoundaryAtom25Two) (w : W) :
    Ge (boundaryNonBoundaryToFullAtom (Sum.inr B)) (F w) 0 ∧
      (w ∈ (fullNonBoundaryAtomEquivHeightOne B).asIdeal →
        Ge (boundaryNonBoundaryToFullAtom (Sum.inr B)) (F w) 1) := by
  by_cases hw : w = 0
  · subst hw
    exact ⟨Or.inl (map_zero _), fun _ => Or.inl (map_zero _)⟩
  have hF : F w ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W K)).mpr hw
  set v := fullNonBoundaryAtomEquivHeightOne B with hv
  letI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ v.ne_bot
      (Localization.AtPrime v.asIdeal)
  have hord : ordAt (boundaryNonBoundaryToFullAtom (Sum.inr B)) (F w) =
      WithZero.log (Ring.ordFrac (Localization.AtPrime v.asIdeal) (F w)) := by
    rw [ordAt_of_ne _ hF]
    simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_nonBoundary,
      nonBoundaryPrincipalDivisor_apply]
    change FractionalIdeal.count K v (FractionalIdeal.spanSingleton W⁰ (F w)) = _
    exact count_spanSingleton_eq_log_ordFrac v (F w) hF
  have hsc : F w = algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap W (Localization.AtPrime v.asIdeal) w) :=
    IsScalarTower.algebraMap_apply W (Localization.AtPrime v.asIdeal) K w
  have ha : algebraMap W (Localization.AtPrime v.asIdeal) w ≠ 0 := fun h =>
    hF (by rw [hsc, h, map_zero])
  refine ⟨Or.inr ?_, fun hm => Or.inr ?_⟩
  · rw [hord, hsc]
    exact dvr_nonneg _ ha
  · rw [hord, hsc]
    exact dvr_pos _ ha
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ v.asIdeal w).mpr hm)

/-- The height-one prime of an `F₂`-point of the chart `w = 1`, given by the
kernel of its evaluation map. -/
def heightOneOfEval (φ : W →ₐ[ZMod 2] ZMod 2) (w₀ : W) (hw₀ : w₀ ≠ 0) (hφ : φ w₀ = 0) :
    WHeightOne where
  asIdeal := RingHom.ker φ
  isPrime := RingHom.ker_isPrime φ
  ne_bot := by
    intro h
    have hmem : w₀ ∈ RingHom.ker φ := RingHom.mem_ker.mpr hφ
    rw [h, Ideal.mem_bot] at hmem
    exact hw₀ hmem

/-- The values of `qy, qz` at an `F₂`-point of the chart with given `qx`
value are forced by the quadric and the cubic. -/
private theorem eval_relations (φ : W →ₐ[ZMod 2] ZMod 2) :
    φ qx * φ qz + φ qx + φ qy ^ 2 + φ qy * φ qz + φ qz = 0 ∧
      φ qx ^ 2 + φ qx * φ qy * φ qz + φ qx * φ qy + φ qx * φ qz + φ qy * φ qz +
        φ qz ^ 2 + φ qz = 0 := by
  have hq := congrArg φ w_quadric_relation
  have hc := congrArg φ w_cubic_relation
  simp only [map_add, map_mul, map_pow, map_zero] at hq hc
  exact ⟨hq, hc⟩

theorem originEval_qy_qz : originEval qy = 0 ∧ originEval qz = 0 := by
  obtain ⟨hq, hc⟩ := eval_relations originEval
  rw [originEval_qx] at hq hc
  revert hq hc
  generalize originEval qy = a
  generalize originEval qz = b
  revert a b
  decide

theorem binaryPointEval_qy_qz : binaryPointEval qy = 1 ∧ binaryPointEval qz = 0 := by
  obtain ⟨hq, hc⟩ := eval_relations binaryPointEval
  rw [binaryPointEval_qx] at hq hc
  revert hq hc
  generalize binaryPointEval qy = a
  generalize binaryPointEval qz = b
  revert a b
  decide

theorem originEval_qy : originEval qy = 0 := originEval_qy_qz.1
theorem originEval_qz : originEval qz = 0 := originEval_qy_qz.2
theorem binaryPointEval_qy : binaryPointEval qy = 1 := binaryPointEval_qy_qz.1
theorem binaryPointEval_qz : binaryPointEval qz = 0 := binaryPointEval_qy_qz.2

/-- The nonboundary atom of `R = [0:0:0:1]`. -/
def nbR : FullNonBoundaryAtom25Two :=
  fullNonBoundaryAtomEquivHeightOne.symm (heightOneOfEval originEval qx qx_ne_zero originEval_qx)

/-- The nonboundary atom of `P = [1:1:0:1]`. -/
def nbP : FullNonBoundaryAtom25Two :=
  fullNonBoundaryAtomEquivHeightOne.symm
    (heightOneOfEval binaryPointEval qz qz_ne_zero binaryPointEval_qz)

/-- The point `R = [0:0:0:1]`. -/
def atomR : fullClosedPointGrading25Two.Atom := boundaryNonBoundaryToFullAtom (Sum.inr nbR)
/-- The point `P = [1:1:0:1]`. -/
def atomP : fullClosedPointGrading25Two.Atom := boundaryNonBoundaryToFullAtom (Sum.inr nbP)

theorem ge_atomR_of_eval (w : W) (hw : originEval w = 0) : Ge atomR (F w) 1 :=
  (ge_nonBoundary nbR w).2 (by
    rw [nbR, Equiv.apply_symm_apply]
    exact RingHom.mem_ker.mpr hw)

theorem ge_atomP_of_eval (w : W) (hw : binaryPointEval w = 0) : Ge atomP (F w) 1 :=
  (ge_nonBoundary nbP w).2 (by
    rw [nbP, Equiv.apply_symm_apply]
    exact RingHom.mem_ker.mpr hw)

theorem nbR_ne_nbP : nbR ≠ nbP := by
  intro h
  have h2 := congrArg (fun B => (fullNonBoundaryAtomEquivHeightOne B).asIdeal) h
  simp only [nbR, nbP, Equiv.apply_symm_apply, heightOneOfEval] at h2
  have hmem : qx ∈ RingHom.ker binaryPointEval := h2 ▸ RingHom.mem_ker.mpr originEval_qx
  rw [RingHom.mem_ker, binaryPointEval_qx] at hmem
  exact one_ne_zero hmem

/-! ## Degrees -/

private theorem atomDegree_of_eval (φ : W →ₐ[ZMod 2] ZMod 2) (w₀ : W) (hw₀ : w₀ ≠ 0)
    (hφ : φ w₀ = 0) :
    fullClosedPointGrading25Two.atomDegree
      (fullNonBoundaryAtomEquivHeightOne.symm (heightOneOfEval φ w₀ hw₀ hφ)).1 = 1 := by
  have h1 := fullNonBoundaryPrimeIdeal_residue_card
    (fullNonBoundaryAtomEquivHeightOne.symm (heightOneOfEval φ w₀ hw₀ hφ))
  have hI : fullNonBoundaryPrimeIdeal
      (fullNonBoundaryAtomEquivHeightOne.symm (heightOneOfEval φ w₀ hw₀ hφ)) = RingHom.ker φ := by
    rw [← fullNonBoundaryAtomEquivHeightOne_asIdeal, Equiv.apply_symm_apply]
    rfl
  rw [hI] at h1
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap (ZMod 2) W c, φ.commutes c⟩
  have hc : Nat.card (W ⧸ RingHom.ker φ) = 2 := by
    rw [Nat.card_congr (Ideal.quotientKerAlgEquivOfSurjective hsurj).toEquiv]
    simp
  rw [hc] at h1
  exact Nat.pow_right_injective (le_refl 2) (by simpa using h1.symm)

theorem atomR_degree : fullClosedPointGrading25Two.atomDegree atomR = 1 :=
  atomDegree_of_eval _ _ _ _

theorem atomP_degree : fullClosedPointGrading25Two.atomDegree atomP = 1 :=
  atomDegree_of_eval _ _ _ _

/-! ## Divisors supported on the five rational points -/

/-- The divisor `cX·X + cYZ·YZ + cZ·Z + cR·R + cP·P`. -/
def lof (cX cYZ cZ cR cP : ℤ) : ProjectiveDivisor25Two :=
  Finsupp.single atomX cX + Finsupp.single atomYZ cYZ + Finsupp.single atomZ cZ +
    Finsupp.single atomR cR + Finsupp.single atomP cP

private theorem divisorDegree_single (A : fullClosedPointGrading25Two.Atom) (c : ℤ) :
    fullClosedPointGrading25Two.divisorDegree (Finsupp.single A c) =
      c * fullClosedPointGrading25Two.atomDegree A := by
  change (Finsupp.single A c).sum
    (fun x m => m * (fullClosedPointGrading25Two.atomDegree x : ℤ)) = _
  rw [Finsupp.sum_single_index (by simp)]

theorem lof_degree (cX cYZ cZ cR cP : ℤ) :
    fullClosedPointGrading25Two.divisorDegree (lof cX cYZ cZ cR cP) =
      cX + cYZ + cZ + cR + cP := by
  simp only [lof, map_add, divisorDegree_single, atomR_degree, atomP_degree, atomX, atomYZ,
    atomZ, boundaryNonBoundaryToFullAtom, fullBoundaryAtomOfTag_degree]
  push_cast
  ring

theorem lof_apply_X (cX cYZ cZ cR cP : ℤ) : lof cX cYZ cZ cR cP atomX = cX := by
  simp [lof, atomX, atomYZ, atomZ, atomR, atomP,
    boundaryNonBoundaryToFullAtom_injective.eq_iff]

theorem lof_apply_YZ (cX cYZ cZ cR cP : ℤ) : lof cX cYZ cZ cR cP atomYZ = cYZ := by
  simp [lof, atomX, atomYZ, atomZ, atomR, atomP,
    boundaryNonBoundaryToFullAtom_injective.eq_iff]

theorem lof_apply_Z (cX cYZ cZ cR cP : ℤ) : lof cX cYZ cZ cR cP atomZ = cZ := by
  simp [lof, atomX, atomYZ, atomZ, atomR, atomP,
    boundaryNonBoundaryToFullAtom_injective.eq_iff]

theorem lof_apply_R (cX cYZ cZ cR cP : ℤ) : lof cX cYZ cZ cR cP atomR = cR := by
  simp [lof, atomX, atomYZ, atomZ, atomR, atomP,
    boundaryNonBoundaryToFullAtom_injective.eq_iff, nbR_ne_nbP.symm]

theorem lof_apply_P (cX cYZ cZ cR cP : ℤ) : lof cX cYZ cZ cR cP atomP = cP := by
  simp [lof, atomX, atomYZ, atomZ, atomR, atomP,
    boundaryNonBoundaryToFullAtom_injective.eq_iff, nbR_ne_nbP]

theorem lof_apply_other (cX cYZ cZ cR cP : ℤ) (B : FullNonBoundaryAtom25Two)
    (hR : B ≠ nbR) (hP : B ≠ nbP) :
    lof cX cYZ cZ cR cP (boundaryNonBoundaryToFullAtom (Sum.inr B)) = 0 := by
  simp [lof, atomX, atomYZ, atomZ, atomR, atomP,
    boundaryNonBoundaryToFullAtom_injective.eq_iff, Ne.symm hR, Ne.symm hP]

/-- **Exact divisors from lower bounds.**  A regular function on the chart
`w = 1` with the given lower bounds at the five rational points, whose
coefficients sum to zero, has exactly that divisor. -/
theorem div_eq_lof (w : W) (hw : F w ≠ 0) (cX cYZ cZ cR cP : ℤ)
    (hsum : cX + cYZ + cZ + cR + cP = 0)
    (hX : Ge atomX (F w) cX) (hYZ : Ge atomYZ (F w) cYZ) (hZ : Ge atomZ (F w) cZ)
    (hR : Ge atomR (F w) cR) (hP : Ge atomP (F w) cP) :
    projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (F w) hw)) =
      lof cX cYZ cZ cR cP := by
  apply principal_eq_of_le (F w) hw _ (by rw [lof_degree]; exact hsum)
  intro A
  obtain ⟨s, rfl⟩ := boundaryNonBoundaryToFullAtom_surjective A
  rcases s with t | B
  · cases t with
    | X => rw [← atomX, lof_apply_X]; exact hX
    | YZ => rw [← atomYZ, lof_apply_YZ]; exact hYZ
    | Z => rw [← atomZ, lof_apply_Z]; exact hZ
  · by_cases hBR : B = nbR
    · subst hBR; rw [← atomR, lof_apply_R]; exact hR
    by_cases hBP : B = nbP
    · subst hBP; rw [← atomP, lof_apply_P]; exact hP
    rw [lof_apply_other _ _ _ _ _ B hBR hBP]
    exact (ge_nonBoundary B w).1

end MazurProof.N25F_RationalPointOrders
