import FLT.Assumptions.MazurProof.N25F_PolynomialBoundaryOrders
import FLT.Assumptions.MazurProof.N25F_BasePolePowers
import FLT.Assumptions.MazurProof.N25F_WChartBaseNorm
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# An explicit reduced F₂[z]-family of the N25 W-chart

Write `x = X/W`, `y = Y/W`, `z = Z/W` for the actual W-chart coordinates and
`B∞ = X + YZ + 2Z` for the pole divisor of the base function `z`. The four
functions

* `b₀ = 1`,
* `b₁ = y`,
* `b₂ = x + z y = (XW + YZ)/W²`,
* `b₃ = x (x + y z + z²) = X (XW + YZ + Z²)/W³`

are linearly independent over `F₂[z]`, and `bᵢ ∈ L(kᵢ B∞)` with weights
`k = (0, 2, 2, 3)`. The weights sum to `7 = g + deg B∞ - 1`, the optimal
value for a curve of genus four, so these windows give the sharp count
`ℓ(n B∞) ≥ 4n - 3`.

*Independence.* Multiplying `Σ pᵢ bᵢ = 0` by `D = xz + x + z`, and using the
cubic `y D = x² + xz + z² + z`, gives a polynomial of degree at most three in
`x` over `F₂[z]`. It vanishes in the plane coordinate ring
`F₂[z][x]/(sextic)`, which embeds in the W-chart, so all its coefficients
vanish. Those four coefficient equations force `pᵢ = 0`.

*Pole bounds.* At `Y Z` and `Z`, the bounds follow from the coordinate
orders alone. At `X`, `x` and `z y` both have pole order three, and the
cubic gives the cancellations

* `b₂ = y + z + (y z + z² + z)/x`;
* `b₃ (x + y) = z x (y + 1)`.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SharpBasis

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

local notation "P" => Polynomial (ZMod 2)
local notation "K" => FractionRing W

/-! ## The chart relations -/

private theorem wChartPoint_eq' :
    chartQuotientPoint (3 : Fin 4) = (⟨qx, qy, qz, 1⟩ : Coordinates4 W) := by
  simp [chartQuotientPoint, mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, qx, qy, qz]

/-- The canonical cubic on the chart `w = 1`. -/
theorem w_cubic_relation :
    qx ^ 2 + qx * qy * qz + qx * qy + qx * qz + qy * qz + qz ^ 2 + qz = (0 : W) := by
  have h := chartQuotientPoint_cubic (3 : Fin 4)
  rw [wChartPoint_eq'] at h
  simpa [canonicalCubic25CharTwo] using h

/-- The canonical quadric on the chart `w = 1`. -/
theorem w_quadric_relation :
    qx * qz + qx + qy ^ 2 + qy * qz + qz = (0 : W) := by
  have h := chartQuotientPoint_quadric (3 : Fin 4)
  rw [wChartPoint_eq'] at h
  simpa [canonicalQuadric25CharTwo] using h

theorem w_two_eq_zero : (2 : W) = 0 := by
  have h : (2 : ZMod 2) = 0 := rfl
  have h2 := congrArg (algebraMap (ZMod 2) W) h
  rwa [map_ofNat, map_zero] at h2

theorem k_two_eq_zero : (2 : K) = 0 := by
  have h := congrArg (algebraMap W K) w_two_eq_zero
  rwa [map_ofNat, map_zero] at h

theorem p_two_eq_zero : (2 : P) = 0 := by
  have h : (2 : ZMod 2) = 0 := rfl
  have h2 := congrArg (algebraMap (ZMod 2) P) h
  rwa [map_ofNat, map_zero] at h2

theorem qx_eq_planeX : qx = algebraMap PlaneCoordinateRing W planeX := by
  change qx = planeCoordinateRingToCanonicalWChart planeX
  rw [planeCoordinateRingToCanonicalWChart_planeX]
  simp [canonicalWChartX, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize, dehomogenizedVariable, qx]

/-! ## The family -/

/-- The explicit reduced family `1, y, x + z y, x (x + y z + z²)`. -/
def sharpBasis : Fin 4 → W :=
  ![1, qy, qx + qz * qy, qx * (qx + qy * qz + qz ^ 2)]

/-- Its pole weights along `B∞`. -/
def sharpWeight : Fin 4 → ℕ := ![0, 2, 2, 3]

theorem sharpWeight_sum : ∑ i, sharpWeight i = 7 := by
  simp [sharpWeight, Fin.sum_univ_four]

/-- Clearing the denominator `D = xz + x + z` turns an `F₂[z]`-relation among
the family into a cubic polynomial in `x`. -/
private theorem cleared_relation (G0 G1 G2 G3 : W) :
    (qx * qz + qx + qz) *
        (G0 + G1 * qy + G2 * (qx + qz * qy) + G3 * (qx * (qx + qy * qz + qz ^ 2))) =
      (G0 * qz + G1 * (qz ^ 2 + qz) + G2 * (qz ^ 3 + qz ^ 2)) +
        (G0 * (qz + 1) + G1 * qz + G2 * (qz ^ 2 + qz) + G3 * qz ^ 2) * qx +
        (G1 + G2 + G3 * (qz ^ 3 + qz)) * qx ^ 2 + G3 * qx ^ 3 := by
  linear_combination (G1 + G2 * qz + G3 * qx * qz) * w_cubic_relation +
    (-G1 * qx ^ 2 - G1 * qx * qz - G1 * qz ^ 2 - G1 * qz - G2 * qx * qz ^ 2 -
      G2 * qz ^ 3 - G2 * qz ^ 2 - G3 * qx * qz ^ 2) * w_two_eq_zero

/-- A polynomial of degree at most three in the plane coordinate `x` vanishes
only when its coefficients do: the plane sextic is monic of degree four. -/
private theorem plane_cubic_coeffs_eq_zero (c0 c1 c2 c3 : P)
    (h : algebraMap P W c0 + algebraMap P W c1 * qx + algebraMap P W c2 * qx ^ 2 +
      algebraMap P W c3 * qx ^ 3 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  let F : P[X] := C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3
  have hA : AdjoinRoot.mk planeSexticPolynomial F = 0 := by
    apply planeCoordinateRingToCanonicalWChart_injective
    rw [map_zero, ← h, qx_eq_planeX]
    simp only [F, map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rfl
  have hF : F = 0 := by
    by_contra hne
    have hdvd : planeSexticPolynomial ∣ F := AdjoinRoot.mk_eq_zero.mp hA
    apply planeSexticPolynomial_monic.not_dvd_of_natDegree_lt hne _ hdvd
    rw [planeSexticPolynomial_natDegree]
    have : F.natDegree ≤ 3 := by
      simp only [F]
      compute_degree
    omega
  have hc (j : ℕ) := congrArg (fun f : P[X] => f.coeff j) hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [F, coeff_X, coeff_X_pow] using hc 0
  · simpa [F, coeff_X, coeff_X_pow] using hc 1
  · simpa [F, coeff_X, coeff_X_pow] using hc 2
  · simpa [F, coeff_X, coeff_X_pow] using hc 3

/-- The explicit family is linearly independent over `F₂[z]`. -/
theorem sharpBasis_linearIndependent : LinearIndependent P sharpBasis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : algebraMap P W (g 0) + algebraMap P W (g 1) * qy +
      algebraMap P W (g 2) * (qx + qz * qy) +
      algebraMap P W (g 3) * (qx * (qx + qy * qz + qz ^ 2)) = 0 := by
    simpa [Fin.sum_univ_four, sharpBasis, Algebra.smul_def] using hg
  have hz : algebraMap P W X = qz := algebraMap_Rz_X
  have hcl := cleared_relation (algebraMap P W (g 0)) (algebraMap P W (g 1))
    (algebraMap P W (g 2)) (algebraMap P W (g 3))
  rw [hsum, mul_zero] at hcl
  obtain ⟨h0, h1, h2, h3⟩ := plane_cubic_coeffs_eq_zero
    (g 0 * X + g 1 * (X ^ 2 + X) + g 2 * (X ^ 3 + X ^ 2))
    (g 0 * (X + 1) + g 1 * X + g 2 * (X ^ 2 + X) + g 3 * X ^ 2)
    (g 1 + g 2 + g 3 * (X ^ 3 + X)) (g 3) (by
      simp only [map_add, map_mul, map_pow, map_one, hz]
      exact hcl.symm)
  have hg2 : g 2 * (X ^ 4 + X ^ 2 + X) = 0 := by
    linear_combination (X + 1) * h0 + X * h1 - (X ^ 3 + X ^ 2 + X) * h2 +
      (X ^ 6 + X ^ 5 + 2 * X ^ 4 + X ^ 2) * h3 +
      (-X ^ 3 * g 2 - X ^ 2 * g 0 - X ^ 2 * g 1 - X * g 0 + X * g 2) * p_two_eq_zero
  have hq : (X ^ 4 + X ^ 2 + X : P) ≠ 0 := by
    intro h
    have := congrArg (fun f : P => f.coeff 1) h
    simp [coeff_X, coeff_X_pow] at this
  have hl : (X + 1 : P) ≠ 0 := by
    intro h
    have := congrArg (fun f : P => f.coeff 0) h
    simp at this
  have e2 : g 2 = 0 := (mul_eq_zero.mp hg2).resolve_right hq
  have e3 : g 3 = 0 := h3
  have e1 : g 1 = 0 := by
    rw [e2, e3] at h2
    simpa using h2
  have e0 : g 0 = 0 := by
    rw [e1, e2, e3] at h1
    simp only [zero_mul, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hl
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem sharpBasis_ne_zero (i : Fin 4) : sharpBasis i ≠ 0 :=
  sharpBasis_linearIndependent.ne_zero i


/-! ## Pole bounds through an ultrametric order

At each boundary point the local order `O : K →*₀ ℤᵐ⁰` (positive on zeros) is
ultrametric. `PoleLE O f k` says that `f` has a pole of order at most `k`. -/

/-- `f` has pole order at most `k` for the order `O` (vacuous for `f = 0`). -/
def PoleLE (O : K →*₀ ℤᵐ⁰) (f : K) (k : ℤ) : Prop := f = 0 ∨ exp (-k) ≤ O f

section PoleLE

variable {O : K →*₀ ℤᵐ⁰}

theorem PoleLE.add (hO : ∀ a b : K, a + b ≠ 0 → min (O a) (O b) ≤ O (a + b))
    {f g : K} {k : ℤ} (hf : PoleLE O f k) (hg : PoleLE O g k) : PoleLE O (f + g) k := by
  by_cases h : f + g = 0
  · exact Or.inl h
  right
  rcases hf with rfl | hf
  · simpa using hg.resolve_left (by simpa using h)
  rcases hg with rfl | hg
  · simpa using hf
  exact (le_min hf hg).trans (hO f g h)

theorem PoleLE.mul {f g : K} {a b : ℤ} (hf : PoleLE O f a) (hg : PoleLE O g b) :
    PoleLE O (f * g) (a + b) := by
  rcases hf with rfl | hf
  · exact Or.inl (zero_mul g)
  rcases hg with rfl | hg
  · exact Or.inl (mul_zero f)
  right
  rw [map_mul, neg_add, exp_add]
  exact mul_le_mul' hf hg

theorem PoleLE.mono {f : K} {k k' : ℤ} (hf : PoleLE O f k) (hk : k ≤ k') :
    PoleLE O f k' :=
  hf.imp_right fun h => (exp_le_exp.mpr (neg_le_neg hk)).trans h

theorem poleLE_of_eq {f : K} {k : ℤ} (h : O f = exp (-k)) : PoleLE O f k :=
  Or.inr h.ge

theorem poleLE_one : PoleLE O 1 0 := poleLE_of_eq (by simp)

/-- Division by a function of exact order `-a` lowers the pole bound by `a`. -/
theorem PoleLE.of_mul_eq {f g h : K} {a c : ℤ} (hg : O g = exp (-a)) (hfg : f * g = h)
    (hh : PoleLE O h c) : PoleLE O f (c - a) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero] at hg
    exact exp_ne_zero hg.symm
  rcases hh with rfl | hh
  · exact Or.inl ((mul_eq_zero.mp hfg).resolve_right hg0)
  right
  rw [← hfg, map_mul, hg] at hh
  have := mul_le_mul_right' hh (exp a)
  rw [mul_assoc, ← exp_add, ← exp_add, neg_add_cancel, exp_zero, mul_one] at this
  rwa [neg_sub, sub_eq_neg_add]

/-- In characteristic two, the strictly smaller order wins in a sum. -/
theorem order_add_eq_of_lt (hO : ∀ a b : K, a + b ≠ 0 → min (O a) (O b) ≤ O (a + b))
    {a b : K} (ha : a ≠ 0) (hab : O a < O b) : O (a + b) = O a := by
  have hb2 : b + b = 0 := by linear_combination b * k_two_eq_zero
  have hsum : a + b ≠ 0 := by
    intro h
    have : b = a := by linear_combination hb2 - h
    rw [this] at hab
    exact lt_irrefl _ hab
  apply le_antisymm
  · have ha' : a + b + b = a := by linear_combination hb2
    have h1 := hO (a + b) b (by rw [ha']; exact ha)
    rw [ha'] at h1
    by_contra hlt
    exact (not_le.mpr (lt_min (not_le.mp hlt) hab)) h1
  · simpa [min_eq_left hab.le] using hO a b hsum

theorem neg_le_log_of_poleLE {f : K} {k : ℤ} (hf0 : f ≠ 0) (hf : PoleLE O f k) :
    -k ≤ log (O f) :=
  (le_log_iff_exp_le ((_root_.map_ne_zero O).mpr hf0)).mpr (hf.resolve_left hf0)

end PoleLE

private theorem ordFrac_image_eq_exp'
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

/-- Elements of a discrete valuation ring have no pole. -/
private theorem ordFrac_integral {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K] (a : R) :
    a = 0 ∨ 1 ≤ Ring.ordFrac R (algebraMap R K a) := by
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  rw [Ring.ordFrac_eq_valuation_inv]
  have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing W)
      (algebraMap R (FractionRing W) a) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  have h0 : 0 < (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K a) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  exact (one_le_inv₀ h0).mpr h1

local notation "F" => algebraMap W K

/-! ## The X point: orders `x ↦ -3`, `y ↦ -2`, `z ↦ -1` -/

local notation "Ox" => xLocalFractionOrder

theorem x_add (a b : K) (h : a + b ≠ 0) : min (Ox a) (Ox b) ≤ Ox (a + b) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  exact Ring.ordFrac_add a b h

theorem x_qx : Ox (F qx) = exp (-3) := by
  have h : log (Ox (F qx)) = -3 := xBoundaryOrder_qx
  rw [← h, exp_log ((_root_.map_ne_zero _).mpr fraction_qx_ne_zero)]

theorem x_qz : Ox (F qz) = exp (-1) := by
  have h : log (Ox (F qz)) = -1 := xBoundaryOrder_qz
  rw [← h, exp_log ((_root_.map_ne_zero _).mpr fraction_qz_ne_zero)]

theorem x_qy : Ox (F qy) = exp (-2) := by
  have himg : xLocalToFraction xYGerm = F qy / F qx := by
    rw [xYGerm, xLocalToFraction_algebraMap, xChartToFraction_xY]
  have hne : xYGerm ≠ 0 := by
    intro h
    rw [h, map_zero] at himg
    exact div_ne_zero fraction_qy_ne_zero fraction_qx_ne_zero himg.symm
  have hY : Ox (xLocalToFraction xYGerm) = exp 1 := by
    letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
    letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
    exact ordFrac_image_eq_exp' (L := K) xYGerm hne 1 xYGerm_ord_eq_one
  have hq : F qy = xLocalToFraction xYGerm * F qx := by
    rw [himg, div_mul_cancel₀ _ fraction_qx_ne_zero]
  rw [hq, map_mul, hY, x_qx, ← exp_add]
  norm_num

/-! ## The YZ point: orders `y, z ↦ -1`, `x ≥ -1` -/

local notation "Oyz" => yzLocalFractionOrder

theorem yz_add (a b : K) (h : a + b ≠ 0) : min (Oyz a) (Oyz b) ≤ Oyz (a + b) := by
  letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
  exact Ring.ordFrac_add a b h

theorem yz_integral (a : YZLocalRing) : PoleLE Oyz (yzLocalToFraction a) 0 := by
  letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
  rcases ordFrac_integral a with h | h
  · left
    rw [h, map_zero]
  · right
    rw [neg_zero, exp_zero]
    exact h

theorem yz_qy : Oyz (F qy) = exp (-1) := by
  have h : log (Oyz (F qy)) = -1 := yzBoundaryOrder_qy
  rw [← h, exp_log ((_root_.map_ne_zero _).mpr fraction_qy_ne_zero)]

theorem yz_qz : Oyz (F qz) = exp (-1) := by
  have h : log (Oyz (F qz)) = -1 := yzBoundaryOrder_qz
  rw [← h, exp_log ((_root_.map_ne_zero _).mpr fraction_qz_ne_zero)]

theorem yz_qx : PoleLE Oyz (F qx) 1 := by
  have hq : F qx = yzLocalToFraction (algebraMap YChartRing YZLocalRing yX) * F qy := by
    rw [yzLocalToFraction_yX, div_mul_cancel₀ _ fraction_qy_ne_zero]
  have h := (yz_integral (algebraMap YChartRing YZLocalRing yX)).mul (poleLE_of_eq yz_qy)
  rwa [zero_add, ← hq] at h

/-! ## The Z point: orders `z ↦ -2`, `x, y ≥ -2` -/

local notation "Oz" => zLocalFractionOrder

theorem z_add (a b : K) (h : a + b ≠ 0) : min (Oz a) (Oz b) ≤ Oz (a + b) := by
  letI : Algebra ZLocalRing K := zLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := zLocalToFraction_isFractionRing
  exact Ring.ordFrac_add a b h

theorem z_integral (a : ZLocalRing) : PoleLE Oz (zLocalToFraction a) 0 := by
  letI : Algebra ZLocalRing K := zLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing K := zLocalToFraction_isFractionRing
  rcases ordFrac_integral a with h | h
  · left
    rw [h, map_zero]
  · right
    rw [neg_zero, exp_zero]
    exact h

theorem z_qz : Oz (F qz) = exp (-2) := by
  have h : log (Oz (F qz)) = -2 := zBoundaryOrder_qz
  rw [← h, exp_log ((_root_.map_ne_zero _).mpr fraction_qz_ne_zero)]

theorem z_qx : PoleLE Oz (F qx) 2 := by
  have hq : F qx = zLocalToFraction (algebraMap ZChartRing ZLocalRing zX) * F qz := by
    rw [zLocalToFraction_algebraMap, zChartToFraction_zX, div_mul_cancel₀ _ fraction_qz_ne_zero]
  have h := (z_integral (algebraMap ZChartRing ZLocalRing zX)).mul (poleLE_of_eq z_qz)
  rwa [zero_add, ← hq] at h

theorem z_qy : PoleLE Oz (F qy) 2 := by
  have hq : F qy = zLocalToFraction (algebraMap ZChartRing ZLocalRing zY) * F qz := by
    rw [zLocalToFraction_algebraMap, zChartToFraction_zY, div_mul_cancel₀ _ fraction_qz_ne_zero]
  have h := (z_integral (algebraMap ZChartRing ZLocalRing zY)).mul (poleLE_of_eq z_qz)
  rwa [zero_add, ← hq] at h


/-! ## The family has the claimed poles -/

theorem F_sharpBasis_zero : F (sharpBasis 0) = 1 := by simp [sharpBasis]
theorem F_sharpBasis_one : F (sharpBasis 1) = F qy := by simp [sharpBasis]
theorem F_sharpBasis_two : F (sharpBasis 2) = F qx + F qz * F qy := by simp [sharpBasis]
theorem F_sharpBasis_three :
    F (sharpBasis 3) = F qx * (F qx + F qy * F qz + F qz * F qz) := by
  simp [sharpBasis, pow_two]

theorem k_cubic :
    F qx ^ 2 + F qx * F qy * F qz + F qx * F qy + F qx * F qz + F qy * F qz +
      F qz ^ 2 + F qz = 0 := by
  have h := congrArg F w_cubic_relation
  simpa only [map_add, map_mul, map_pow, map_zero] using h

theorem k_quadric : F qx * F qz + F qx + F qy ^ 2 + F qy * F qz + F qz = 0 := by
  have h := congrArg F w_quadric_relation
  simpa only [map_add, map_mul, map_pow, map_zero] using h

/-- The cancellation identity for `b₃` at `X`, from the quadric and cubic. -/
theorem w_b3_relation :
    qx * (qx + qy * qz + qz * qz) * (qx + qy) = qz * qx * (qy + 1) := by
  linear_combination qx * qz * w_quadric_relation + qx * w_cubic_relation -
    (qx ^ 2 * qz + qx * qy * qz + qx * qz ^ 2 + qx * qz) * w_two_eq_zero

set_option maxHeartbeats 1000000 in
/-- At `X`, `x` and `z y` both have a pole of order three, but their sum
`b₂` only has a pole of order two: `(b₂ + y + z) x = y z + z² + z`. Likewise
`b₃ (x + y) = z x (y + 1)` with `x + y` of exact pole order three. -/
theorem sharpBasis_poleX (i : Fin 4) : PoleLE Ox (F (sharpBasis i)) (sharpWeight i) := by
  have hqx : PoleLE Ox (F qx) 3 := poleLE_of_eq x_qx
  have hqy : PoleLE Ox (F qy) 2 := poleLE_of_eq x_qy
  have hqz : PoleLE Ox (F qz) 1 := poleLE_of_eq x_qz
  fin_cases i
  · change PoleLE Ox (F (sharpBasis 0)) ((sharpWeight 0 : ℕ) : ℤ)
    rw [F_sharpBasis_zero]
    exact poleLE_one.mono (by simp [sharpWeight])
  · change PoleLE Ox (F (sharpBasis 1)) ((sharpWeight 1 : ℕ) : ℤ)
    rw [F_sharpBasis_one]
    exact hqy.mono (by simp [sharpWeight])
  · change PoleLE Ox (F (sharpBasis 2)) ((sharpWeight 2 : ℕ) : ℤ)
    rw [F_sharpBasis_two]
    have hrel : (F qx + F qz * F qy + F qy + F qz) * F qx =
        F qy * F qz + F qz * F qz + F qz := by
      linear_combination k_cubic - (F qy * F qz + F qz * F qz + F qz) * k_two_eq_zero
    have hR : PoleLE Ox (F qy * F qz + F qz * F qz + F qz) 3 :=
      (((hqy.mul hqz).mono (by norm_num)).add x_add ((hqz.mul hqz).mono (by norm_num))).add
        x_add (hqz.mono (by norm_num))
    have hr := PoleLE.of_mul_eq x_qx hrel hR
    have he : F qx + F qz * F qy = (F qx + F qz * F qy + F qy + F qz) + F qy + F qz := by
      linear_combination (-(F qy + F qz)) * k_two_eq_zero
    rw [he]
    exact (((hr.mono (by norm_num)).add x_add hqy).add x_add (hqz.mono (by norm_num))).mono
      (by simp [sharpWeight])
  · change PoleLE Ox (F (sharpBasis 3)) ((sharpWeight 3 : ℕ) : ℤ)
    rw [F_sharpBasis_three]
    have hs : Ox (F qx + F qy) = exp (-3) := by
      rw [order_add_eq_of_lt (a := F qx) (b := F qy) x_add fraction_qx_ne_zero
        (by rw [x_qx, x_qy]; exact exp_lt_exp.mpr (by norm_num)), x_qx]
    have hrel : F qx * (F qx + F qy * F qz + F qz * F qz) * (F qx + F qy) =
        F qz * F qx * (F qy + 1) := by
      have h := congrArg F w_b3_relation
      simpa only [map_add, map_mul, map_one] using h
    have h1 : PoleLE Ox 1 2 := poleLE_one.mono (by norm_num)
    have hy1 : PoleLE Ox (F qy + 1) 2 := hqy.add x_add h1
    have hzx : PoleLE Ox (F qz * F qx) 4 := hqz.mul hqx
    have hR : PoleLE Ox (F qz * F qx * (F qy + 1)) 6 := hzx.mul hy1
    exact (PoleLE.of_mul_eq hs hrel hR).mono (by simp [sharpWeight])

theorem sharpBasis_poleYZ (i : Fin 4) : PoleLE Oyz (F (sharpBasis i)) (sharpWeight i) := by
  have hqx : PoleLE Oyz (F qx) 1 := yz_qx
  have hqy : PoleLE Oyz (F qy) 1 := poleLE_of_eq yz_qy
  have hqz : PoleLE Oyz (F qz) 1 := poleLE_of_eq yz_qz
  fin_cases i
  · change PoleLE Oyz (F (sharpBasis 0)) ((sharpWeight 0 : ℕ) : ℤ)
    rw [F_sharpBasis_zero]
    exact poleLE_one.mono (by simp [sharpWeight])
  · change PoleLE Oyz (F (sharpBasis 1)) ((sharpWeight 1 : ℕ) : ℤ)
    rw [F_sharpBasis_one]
    exact hqy.mono (by simp [sharpWeight])
  · change PoleLE Oyz (F (sharpBasis 2)) ((sharpWeight 2 : ℕ) : ℤ)
    rw [F_sharpBasis_two]
    exact ((hqx.mono (by norm_num)).add yz_add (hqz.mul hqy)).mono (by simp [sharpWeight])
  · change PoleLE Oyz (F (sharpBasis 3)) ((sharpWeight 3 : ℕ) : ℤ)
    rw [F_sharpBasis_three]
    exact (hqx.mul ((((hqx.mono (by norm_num)).add yz_add (hqy.mul hqz)).add yz_add
      (hqz.mul hqz)))).mono (by simp [sharpWeight])

theorem sharpBasis_poleZ (i : Fin 4) :
    PoleLE Oz (F (sharpBasis i)) (2 * sharpWeight i) := by
  have hqx : PoleLE Oz (F qx) 2 := z_qx
  have hqy : PoleLE Oz (F qy) 2 := z_qy
  have hqz : PoleLE Oz (F qz) 2 := poleLE_of_eq z_qz
  fin_cases i
  · change PoleLE Oz (F (sharpBasis 0)) (2 * ((sharpWeight 0 : ℕ) : ℤ))
    rw [F_sharpBasis_zero]
    exact poleLE_one.mono (by simp [sharpWeight])
  · change PoleLE Oz (F (sharpBasis 1)) (2 * ((sharpWeight 1 : ℕ) : ℤ))
    rw [F_sharpBasis_one]
    exact hqy.mono (by simp [sharpWeight])
  · change PoleLE Oz (F (sharpBasis 2)) (2 * ((sharpWeight 2 : ℕ) : ℤ))
    rw [F_sharpBasis_two]
    exact ((hqx.mono (by norm_num)).add z_add (hqz.mul hqy)).mono (by simp [sharpWeight])
  · change PoleLE Oz (F (sharpBasis 3)) (2 * ((sharpWeight 3 : ℕ) : ℤ))
    rw [F_sharpBasis_three]
    exact (hqx.mul ((((hqx.mono (by norm_num)).add z_add (hqy.mul hqz)).add z_add
      (hqz.mul hqz)))).mono (by simp [sharpWeight])

/-- Each member of the family lies in its Riemann–Roch window:
`bᵢ ∈ L(kᵢ B∞)`. -/
theorem sharpBasis_mem (i : Fin 4) :
    F (sharpBasis i) ∈
      fullRiemannRochSpace25Two ((sharpWeight i : ℤ) • basePoleDivisor25Two) := by
  have hne : F (sharpBasis i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W K)).mpr (sharpBasis_ne_zero i)
  have h := regular_function_mem_basePole_space (sharpWeight i) (sharpBasis i)
    (sharpBasis_ne_zero i) (Additive.ofMul (Units.mk0 _ hne)) rfl
    (neg_le_log_of_poleLE hne (sharpBasis_poleX i))
    (neg_le_log_of_poleLE hne (sharpBasis_poleYZ i))
    (neg_le_log_of_poleLE hne (sharpBasis_poleZ i))
  exact h

end MazurProof.N25F_SharpBasis
