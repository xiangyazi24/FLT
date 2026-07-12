import FLT.Assumptions.MazurProof.BillingMahlerField
import FLT.Assumptions.MazurProof.RationalPointsN11Descent
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import scratch.KeystoneEDS
import scratch.TateZ2xZ10Reduction

/-!
# The ideal-square step in the Billing--Mahler descent

This file contains the prime-ideal bookkeeping for the cubic factor used in
the order-eleven descent.  The integral generator is the element `alpha` from
`BillingMahlerField`; its power basis is the full ring-of-integers basis, so
Dedekind--Kummer applies at every rational prime.
-/

namespace MazurProof.RationalPointsN11IdealSquare

open Polynomial
open scoped NumberField
open UniqueFactorizationMonoid
open scoped WeierstrassCurve.Affine
open Scratch.TateZ2xZ10Reduction

attribute [local instance] Ideal.Quotient.field

abbrev K := BillingMahlerField.K
abbrev OK := NumberField.RingOfIntegers K

abbrev ResidueInt (p : ℕ) := ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)

def mordellCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -432
  a₆ := 8208

theorem mordellCurve_delta : mordellCurve.Δ = (-23944605696 : ℚ) := by
  norm_num [mordellCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance mordellCurve_isElliptic : mordellCurve.IsElliptic where
  isUnit := by rw [mordellCurve_delta]; norm_num

def minimalCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1
  a₃ := 1
  a₄ := 0
  a₆ := 0

theorem minimalCurve_delta : minimalCurve.Δ = (-11 : ℚ) := by
  norm_num [minimalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance minimalCurve_isElliptic : minimalCurve.IsElliptic where
  isUnit := by rw [minimalCurve_delta]; norm_num

def mordellToMinimalChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 6 (by norm_num)
  r := -12
  s := 0
  t := 108

theorem mordellToMinimalChange_smul :
    mordellToMinimalChange • mordellCurve = minimalCurve := by
  ext <;> norm_num [mordellToMinimalChange, mordellCurve, minimalCurve,
    WeierstrassCurve.variableChange_def]

abbrev MinimalWeierstrass : WeierstrassCurve ℚ := minimalCurve

abbrev MinimalCurveBase : WeierstrassCurve.Affine ℚ := MinimalWeierstrass⁄ℚ

abbrev MinimalPoint := MinimalCurveBase.Point

private noncomputable def pointCurveEqAddEquiv
    [DecidableEq ℚ] {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+
      WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private noncomputable def affinePointCurveEqAddEquiv
    [DecidableEq ℚ] {W W' : WeierstrassCurve.Affine ℚ} (h : W = W') :
    W.Point ≃+ W'.Point := by
  subst h
  exact AddEquiv.refl _

private theorem pointCurveEqAddEquiv_some
    [DecidableEq ℚ] {W W' : WeierstrassCurve ℚ} (e : W = W')
    {x y : ℚ} (h : WeierstrassCurve.Affine.Nonsingular W x y) :
    ∃ h' : WeierstrassCurve.Affine.Nonsingular W' x y,
      pointCurveEqAddEquiv e
          (WeierstrassCurve.Affine.Point.some x y h) =
        WeierstrassCurve.Affine.Point.some x y h' := by
  subst W'
  exact ⟨h, rfl⟩

private theorem affinePointCurveEqAddEquiv_some
    [DecidableEq ℚ] {W W' : WeierstrassCurve.Affine ℚ} (e : W = W')
    {x y : ℚ} (h : W.Nonsingular x y) :
    ∃ h' : W'.Nonsingular x y,
      affinePointCurveEqAddEquiv e
          (WeierstrassCurve.Affine.Point.some x y h) =
        WeierstrassCurve.Affine.Point.some x y h' := by
  subst W'
  exact ⟨h, rfl⟩

private theorem minimalCurveBase_eq :
    MinimalCurveBase = minimalCurve.toAffine := by
  ext <;> simp [MinimalCurveBase]

private theorem variableChange_slope_of_X_ne_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x1 x2 y1 y2 : ℚ} (hx : x1 ≠ x2) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x1) (variableChangePointX C x2)
        (variableChangePointY C x1 y1) (variableChangePointY C x2 y2) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x1 x2 y1 y2 - C.s) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  · unfold variableChangePointX variableChangePointY
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero, sub_ne_zero.mpr hx]
    ring
  · exact fun h => hx ((variableChangePointX_eq_iff C).mp h)

private theorem variableChange_slope_of_Y_ne_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x1 x2 y1 y2 : ℚ}
    (h1 : WeierstrassCurve.Affine.Equation W x1 y1)
    (h2 : WeierstrassCurve.Affine.Equation W x2 y2)
    (hx : x1 = x2) (hy : y1 ≠ WeierstrassCurve.Affine.negY W x2 y2) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x1) (variableChangePointX C x2)
        (variableChangePointY C x1 y1) (variableChangePointY C x2 y2) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x1 x2 y1 y2 - C.s) := by
  have hyEq : y1 = y2 :=
    WeierstrassCurve.Affine.Y_eq_of_Y_ne h1 h2 hx hy
  have hySelf : y1 ≠ WeierstrassCurve.Affine.negY W x1 y1 := by
    intro h
    apply hy
    rw [← hx, ← hyEq]
    exact h
  have hden : x1 * W.a₁ + W.a₃ + y1 * 2 ≠ 0 := by
    intro hden
    apply hySelf
    rw [WeierstrassCurve.Affine.negY]
    linarith
  have hmul :
      (x1 * W.a₁ + W.a₃ + y1 * 2) *
          (x1 * W.a₁ + W.a₃ + y1 * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have htargetX :
      variableChangePointX C x1 = variableChangePointX C x2 := by
    simp [hx]
  have htargetY :
      variableChangePointY C x1 y1 ≠
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x2) (variableChangePointY C x2 y2) := by
    intro h
    apply hy
    rw [← hx]
    apply (variableChangePointY_eq_iff C x1).mp
    rw [h, hx, variableChangePointY_negY]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne htargetX htargetY]
  unfold variableChangePointX variableChangePointY
  simp [WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  convert
    (show C.s *
        (1 - (x1 * W.a₁ + W.a₃ + y1 * 2) *
          (x1 * W.a₁ + W.a₃ + y1 * 2)⁻¹) = 0 by
      rw [hmul]
      ring) using 1
  ring

private theorem variableChange_slope_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x1 x2 y1 y2 : ℚ}
    (h1 : WeierstrassCurve.Affine.Equation W x1 y1)
    (h2 : WeierstrassCurve.Affine.Equation W x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = WeierstrassCurve.Affine.negY W x2 y2)) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x1) (variableChangePointX C x2)
        (variableChangePointY C x1 y1) (variableChangePointY C x2 y2) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x1 x2 y1 y2 - C.s) := by
  by_cases hx : x1 = x2
  · exact variableChange_slope_of_Y_ne_generic W C h1 h2 hx
      (fun hy => hxy ⟨hx, hy⟩)
  · exact variableChange_slope_of_X_ne_generic W C hx

private theorem variableChangePointMap_add_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point W) :
    Scratch.TateZ2xZ10Reduction.variableChangePointMap W C (P + Q) =
      Scratch.TateZ2xZ10Reduction.variableChangePointMap W C P +
        Scratch.TateZ2xZ10Reduction.variableChangePointMap W C Q := by
  cases P with
  | zero => rfl
  | some x1 y1 h1 =>
    cases Q with
    | zero => rfl
    | some x2 y2 h2 =>
      by_cases hxy : x1 = x2 ∧
          y1 = WeierstrassCurve.Affine.negY W x2 y2
      · have htarget := variableChange_vertical W C hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq
          htarget.left htarget.right]
      · have htarget := variableChange_nonvertical W C hxy
        have hslope := variableChange_slope_generic W C h1.left h2.left hxy
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_some htarget]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · let l : ℚ := WeierstrassCurve.Affine.slope W x1 x2 y1 y2
          let L : ℚ := WeierstrassCurve.Affine.slope (C • W)
            (variableChangePointX C x1) (variableChangePointX C x2)
            (variableChangePointY C x1 y1) (variableChangePointY C x2 y2)
          change variableChangePointX C
              (WeierstrassCurve.Affine.addX W x1 x2 l) =
            WeierstrassCurve.Affine.addX (C • W)
              (variableChangePointX C x1) (variableChangePointX C x2) L
          calc
            _ = WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2)
                ((C.u : ℚ)⁻¹ * (l - C.s)) :=
              variableChange_addX W C x1 x2 l
            _ = _ := by
              apply congrArg (fun t : ℚ ↦ WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2) t)
              simpa only [l, L] using hslope.symm
        · let l : ℚ := WeierstrassCurve.Affine.slope W x1 x2 y1 y2
          let L : ℚ := WeierstrassCurve.Affine.slope (C • W)
            (variableChangePointX C x1) (variableChangePointX C x2)
            (variableChangePointY C x1 y1) (variableChangePointY C x2 y2)
          change variableChangePointY C
              (WeierstrassCurve.Affine.addX W x1 x2 l)
              (WeierstrassCurve.Affine.addY W x1 x2 y1 l) =
            WeierstrassCurve.Affine.addY (C • W)
              (variableChangePointX C x1) (variableChangePointX C x2)
              (variableChangePointY C x1 y1) L
          calc
            _ = WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2)
                (variableChangePointY C x1 y1)
                ((C.u : ℚ)⁻¹ * (l - C.s)) :=
              variableChange_addY W C x1 x2 y1 l
            _ = _ := by
              apply congrArg (fun t : ℚ ↦ WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2)
                (variableChangePointY C x1 y1) t)
              simpa only [l, L] using hslope.symm

noncomputable def mordellToMinimalPointAddEquiv [DecidableEq ℚ] :
    WeierstrassCurve.Affine.Point mordellCurve ≃+ MinimalPoint :=
  (AddEquiv.mk
    (Scratch.TateZ2xZ10Reduction.variableChangePointEquiv
      mordellCurve mordellToMinimalChange)
    (variableChangePointMap_add_generic mordellCurve mordellToMinimalChange)).trans
      ((pointCurveEqAddEquiv mordellToMinimalChange_smul).trans
        (affinePointCurveEqAddEquiv minimalCurveBase_eq.symm))

@[simp] theorem mordellCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation mordellCurve x y ↔
      y ^ 2 = x ^ 3 - 432 * x + 8208 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [mordellCurve]
  ring_nf

@[simp] theorem minimalCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation minimalCurve x y ↔
      y ^ 2 + y = x ^ 3 - x ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [minimalCurve]
  ring_nf

noncomputable def mordellPoint (x y : ℚ)
    (h : y ^ 2 = x ^ 3 - 432 * x + 8208) :
    WeierstrassCurve.Affine.Point mordellCurve :=
  WeierstrassCurve.Affine.Point.some x y
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((mordellCurve_equation_iff x y).2 h))

private theorem exists_mordell_half_of_line
    [DecidableEq ℚ]
    {xi eta u m n : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208)
    (h₂ : -m ^ 2 + 2 * u + xi = 0)
    (h₁ : -432 - 2 * m * n - u ^ 2 - 2 * xi * u = 0)
    (h₀ : 8208 - n ^ 2 + xi * u ^ 2 = 0)
    (hsign : m * xi + n = -eta) :
    ∃ Q : WeierstrassCurve.Affine.Point mordellCurve,
      (2 : ℕ) • Q = mordellPoint xi eta hcurve := by
  let v : ℚ := m * u + n
  have hQcurve : v ^ 2 = u ^ 3 - 432 * u + 8208 := by
    dsimp [v]
    linear_combination -(u ^ 2 * h₂ + u * h₁ + h₀)
  have htangent : 3 * u ^ 2 - 432 = 2 * m * v := by
    dsimp [v]
    linear_combination 2 * u * h₂ + h₁
  have hv : v ≠ 0 := by
    intro hv0
    have huSq : u ^ 2 = 12 ^ 2 := by
      rw [hv0] at htangent
      norm_num at htangent ⊢
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp huSq with hu | hu
    · norm_num [hu, hv0] at hQcurve
    · norm_num [hu, hv0] at hQcurve
  have hYne : v ≠ WeierstrassCurve.Affine.negY mordellCurve u v := by
    rw [WeierstrassCurve.Affine.negY]
    simp only [mordellCurve, zero_mul, zero_add]
    intro h
    apply hv
    linarith
  have hslope :
      WeierstrassCurve.Affine.slope mordellCurve u u v v = m := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hYne]
    simp [WeierstrassCurve.Affine.negY, mordellCurve]
    field_simp [hv]
    nlinarith [htangent]
  let hQ : WeierstrassCurve.Affine.Nonsingular mordellCurve u v :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((mordellCurve_equation_iff u v).2 hQcurve)
  let Q : WeierstrassCurve.Affine.Point mordellCurve :=
    WeierstrassCurve.Affine.Point.some u v hQ
  refine ⟨Q, ?_⟩
  rw [two_nsmul]
  change
    (WeierstrassCurve.Affine.Point.some u v hQ :
      WeierstrassCurve.Affine.Point mordellCurve) +
        WeierstrassCurve.Affine.Point.some u v hQ = _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hQ) hYne]
  unfold mordellPoint
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp only [hslope]
    simp [WeierstrassCurve.Affine.addX, mordellCurve]
    nlinarith [h₂]
  · simp only [hslope]
    simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      mordellCurve, mordellPoint]
    dsimp [v]
    linear_combination m * h₂ - hsign

/-- The explicit Kummer-exactness direction for the Billing--Mahler cubic:
if the cubic factor of a point on the short Mordell model is a square, then
the point has a rational half. -/
theorem exists_mordell_half_of_factor_square
    [DecidableEq ℚ]
    {xi eta : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208)
    (hsquare : IsSquare
      (BillingMahlerField.ofCoords (xi - 24) 18 0)) :
    ∃ Q : WeierstrassCurve.Affine.Point mordellCurve,
      (2 : ℕ) • Q = mordellPoint xi eta hcurve := by
  rcases hsquare with ⟨gamma, hgamma⟩
  obtain ⟨a, b, c, hcoords⟩ := BillingMahlerField.exists_ofCoords gamma
  have hsquareCoords :
      BillingMahlerField.ofCoords (xi - 24) 18 0 =
        BillingMahlerField.ofCoords a b c ^ 2 := by
    rw [← hcoords]
    simpa [pow_two] using hgamma
  rw [BillingMahlerField.ofCoords_sq] at hsquareCoords
  have hzero := congrArg
    (fun q : K ↦ BillingMahlerField.basis.repr q (0 : Fin 3)) hsquareCoords
  have hone := congrArg
    (fun q : K ↦ BillingMahlerField.basis.repr q (1 : Fin 3)) hsquareCoords
  have htwo := congrArg
    (fun q : K ↦ BillingMahlerField.basis.repr q (2 : Fin 3)) hsquareCoords
  simp only [BillingMahlerField.basis_repr_ofCoords_zero] at hzero
  simp only [BillingMahlerField.basis_repr_ofCoords_one] at hone
  simp only [BillingMahlerField.basis_repr_ofCoords_two] at htwo
  have hezero :
      a ^ 2 + 4 * b * c + 8 * c ^ 2 - xi + 24 = 0 := by
    linarith
  have heone :
      2 * a * b - 8 * b * c - 14 * c ^ 2 - 18 = 0 := by
    linarith
  have hetwo :
      b ^ 2 + 2 * a * c + 8 * b * c + 12 * c ^ 2 = 0 := by
    linarith
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    norm_num at hetwo
    have hb : b = 0 := hetwo
    subst b
    norm_num at heone
  have hg :
      b ^ 3 + 8 * b ^ 2 * c + 20 * b * c ^ 2 + 14 * c ^ 3 + 18 * c = 0 := by
    linear_combination b * hetwo - c * heone
  let U : ℚ := -48 * c - 18 * b
  let M : ℚ := a * c - 4 * b * c - b ^ 2 - 4 * c ^ 2
  let N : ℚ := 48 * a * c + 96 * b * c + 60 * c ^ 2 +
    18 * a * b + 24 * b ^ 2
  let u : ℚ := U / c
  let m : ℚ := M / c
  let n : ℚ := N / c
  have hscaled₂ : -M ^ 2 + 2 * U * c + xi * c ^ 2 = 0 := by
    dsimp [U, M]
    linear_combination
      -(c ^ 2) * hezero + c * (b + 4 * c) * heone +
        4 * c ^ 2 * hetwo - b * hg
  have hscaled₁ :
      -432 * c ^ 2 - 2 * M * N - U ^ 2 - 2 * xi * U * c = 0 := by
    dsimp [U, M, N]
    linear_combination
      (-12 * c * (3 * b + 8 * c)) * hezero +
        (6 * (3 * b ^ 2 + 16 * b * c + 28 * c ^ 2)) * heone +
        132 * c ^ 2 * hetwo + 48 * (b + 3 * c) * hg
  have hscaled₀ : 8208 * c ^ 2 - N ^ 2 + xi * U ^ 2 = 0 := by
    dsimp [U, N]
    linear_combination
      (-36 * (3 * b + 8 * c) ^ 2) * hezero +
        (-72 * (6 * b ^ 2 + 40 * b * c + 79 * c ^ 2)) * heone +
        (-2880 * c ^ 2) * hetwo - 144 * (4 * b + 15 * c) * hg
  have hcoef₂ : -m ^ 2 + 2 * u + xi = 0 := by
    dsimp [m, u]
    field_simp [hc]
    convert hscaled₂ using 1 <;> ring
  have hcoef₁ : -432 - 2 * m * n - u ^ 2 - 2 * xi * u = 0 := by
    dsimp [m, n, u]
    field_simp [hc]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled₁
  have hcoef₀ : 8208 - n ^ 2 + xi * u ^ 2 = 0 := by
    dsimp [n, u]
    field_simp [hc]
    simpa using hscaled₀
  have hlineAtXi :
      xi ^ 3 - 432 * xi + 8208 - (m * xi + n) ^ 2 = 0 := by
    linear_combination xi ^ 2 * hcoef₂ + xi * hcoef₁ + hcoef₀
  have hlineSq : (m * xi + n) ^ 2 = eta ^ 2 := by
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hlineSq with hsign | hsign
  · apply exists_mordell_half_of_line hcurve
      (u := u) (m := -m) (n := -n)
    · simpa using hcoef₂
    · simpa using hcoef₁
    · simpa using hcoef₀
    · linear_combination -hsign
  · exact exists_mordell_half_of_line hcurve hcoef₂ hcoef₁ hcoef₀ hsign

/-! ## Explicit division-polynomial certificates at two -/

def divS {R : Type*} [CommRing R] (x : R) : R :=
  4 * x ^ 3 - 4 * x ^ 2 + 1

def divP {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1

def divQ {R : Type*} [CommRing R] (x : R) : R :=
  2 * x ^ 6 - 4 * x ^ 5 + 10 * x ^ 3 - 10 * x ^ 2 + 4 * x - 1

def divR {R : Type*} [CommRing R] (x : R) : R :=
  divS x ^ 2 * divQ x - divP x ^ 3

def divPhi5 {R : Type*} [CommRing R] (x : R) : R :=
  x * divR x ^ 2 -
    divP x * divS x * divQ x * (divR x - divQ x ^ 2)

def divPhi2 {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 4 - 2 * x + 1

def divSH {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 - 4 * a ^ 2 * b + b ^ 3

def divPH {R : Type*} [CommRing R] (a b : R) : R :=
  3 * a ^ 4 - 4 * a ^ 3 * b + 3 * a * b ^ 3 - b ^ 4

def divQH {R : Type*} [CommRing R] (a b : R) : R :=
  2 * a ^ 6 - 4 * a ^ 5 * b + 10 * a ^ 3 * b ^ 3 -
    10 * a ^ 2 * b ^ 4 + 4 * a * b ^ 5 - b ^ 6

def divRH {R : Type*} [CommRing R] (a b : R) : R :=
  divSH a b ^ 2 * divQH a b - divPH a b ^ 3

def divPhi5H {R : Type*} [CommRing R] (a b : R) : R :=
  a * divRH a b ^ 2 -
    divPH a b * divSH a b * divQH a b *
      (divRH a b - divQH a b ^ 2)

private theorem divRH_dehom (a b : ℚ) (hb : b ≠ 0) :
    divRH a b = b ^ 12 * divR (a / b) := by
  unfold divRH divSH divPH divQH divR divS divP divQ
  field_simp [hb]
  <;> ring

private theorem divPhi5H_dehom (a b : ℚ) (hb : b ≠ 0) :
    divPhi5H a b = b ^ 25 * divPhi5 (a / b) := by
  unfold divPhi5H divRH divSH divPH divQH
    divPhi5 divR divS divP divQ
  field_simp [hb]
  <;> ring

private theorem mod_two_five_certificate :
    ∀ a b : ZMod 2, b ≠ 0 →
      divRH a b = 0 ∧ divPhi5H a b = 1 := by
  decide

theorem minimalCurve_PsiSq_five_eval (x : ℚ) :
    (minimalCurve.ΨSq (5 : ℤ)).eval x = divR x ^ 2 := by
  change (minimalCurve.ΨSq ((5 : ℕ) : ℤ)).eval x = divR x ^ 2
  rw [minimalCurve.ΨSq_ofNat 5]
  simp only [show ¬Even (5 : ℕ) by decide, if_false, mul_one,
    Polynomial.eval_pow]
  rw [show 5 = 2 * (0 + 2) + 1 by norm_num,
    minimalCurve.preΨ'_odd 0]
  simp [divR, divS, divP, divQ, minimalCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem minimalCurve_Phi_five_eval (x : ℚ) :
    (minimalCurve.Φ (5 : ℤ)).eval x = divPhi5 x := by
  rw [show (5 : ℤ) = ((4 : ℕ) + 1 : ℤ) by norm_num,
    minimalCurve.Φ_ofNat 4]
  simp only [Nat.reduceAdd, show Even (4 : ℕ) by decide, if_pos, mul_one]
  rw [show 6 = 2 * (0 + 3) by norm_num,
    minimalCurve.preΨ'_even 0]
  rw [show 5 = 2 * (0 + 2) + 1 by norm_num,
    minimalCurve.preΨ'_odd 0]
  simp [divPhi5, divR, divS, divP, divQ, minimalCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem minimalCurve_PsiSq_two_eval (x : ℚ) :
    (minimalCurve.ΨSq (2 : ℤ)).eval x = divS x := by
  rw [minimalCurve.ΨSq_two]
  simp [divS, minimalCurve, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

theorem minimalCurve_Phi_two_eval (x : ℚ) :
    (minimalCurve.Φ (2 : ℤ)).eval x = divPhi2 x := by
  rw [minimalCurve.Φ_two]
  simp [divPhi2, minimalCurve, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private theorem v2_add_eq_left_of_lt
    {a b : ℚ} (ha : a ≠ 0)
    (h : padicValRat 2 a < padicValRat 2 b) :
    padicValRat 2 (a + b) = padicValRat 2 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hz
    have hba : b = -a := by linarith
    rw [hba, padicValRat.neg] at h
    exact (lt_irrefl _ h)
  exact padicValRat.add_eq_of_lt hab ha hb h

private theorem v2_list_sum_zero_or_gt
    (a : ℚ) (L : List ℚ)
    (hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q) :
    L.sum = 0 ∨ padicValRat 2 a < padicValRat 2 L.sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
      have hq : padicValRat 2 a < padicValRat 2 q := hL q (by simp)
      have htail : ∀ r ∈ L, padicValRat 2 a < padicValRat 2 r := by
        intro r hr
        exact hL r (by simp [hr])
      rcases ih htail with hzero | hgt
      · rw [List.sum_cons, hzero, add_zero]
        by_cases hq0 : q = 0
        · exact Or.inl hq0
        · exact Or.inr hq
      · rw [List.sum_cons]
        by_cases hsum : q + L.sum = 0
        · exact Or.inl hsum
        · exact Or.inr (padicValRat.lt_add_of_lt hsum hq hgt)

private theorem v2_add_list_sum_eq
    {a : ℚ} (ha : a ≠ 0) (L : List ℚ)
    (hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q) :
    padicValRat 2 (a + L.sum) = padicValRat 2 a := by
  rcases v2_list_sum_zero_or_gt a L hL with hzero | hgt
  · simp [hzero]
  · exact v2_add_eq_left_of_lt ha hgt

private theorem v2_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact padicValRat.self (by norm_num)

private theorem v2_three : padicValRat 2 (3 : ℚ) = 0 := by
  change padicValRat 2 ((3 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (p := 2) (n := 3) (by norm_num)

private theorem v2_five : padicValRat 2 (5 : ℚ) = 0 := by
  change padicValRat 2 ((5 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (p := 2) (n := 5) (by norm_num)

private theorem v2_four : padicValRat 2 (4 : ℚ) = 2 := by
  calc
    padicValRat 2 (4 : ℚ) = padicValRat 2 ((2 : ℚ) ^ 2) := by norm_num
    _ = (2 : ℤ) * padicValRat 2 (2 : ℚ) :=
      padicValRat.pow (by norm_num)
    _ = 2 := by rw [v2_two]; norm_num

private theorem v2_ten : padicValRat 2 (10 : ℚ) = 1 := by
  calc
    padicValRat 2 (10 : ℚ) = padicValRat 2 ((2 : ℚ) * 5) := by norm_num
    _ = padicValRat 2 (2 : ℚ) + padicValRat 2 (5 : ℚ) :=
      padicValRat.mul (by norm_num) (by norm_num)
    _ = 1 := by rw [v2_two, v2_five]; norm_num

private theorem divS_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divS x ≠ 0 ∧ padicValRat 2 (divS x) = 3 * padicValRat 2 x + 2 := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := 4 * x ^ 3
  let L : List ℚ := [-4 * x ^ 2, 1]
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hx0)
  have hva : padicValRat 2 a = 3 * padicValRat 2 x + 2 := by
    dsimp [a]
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 3 hx0),
      padicValRat.pow hx0, v2_four]
    ring
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 2 hx0),
        padicValRat.pow hx0, v2_four, hva]
      omega
    · rw [padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divS x := by
    simp [a, L, divS]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divP_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divP x ≠ 0 ∧ padicValRat 2 (divP x) = 4 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := 3 * x ^ 4
  let L : List ℚ := [-4 * x ^ 3, 3 * x, -1]
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
  have hva : padicValRat 2 a = 4 * padicValRat 2 x := by
    dsimp [a]
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 4 hx0),
      padicValRat.pow hx0, v2_three]
    ring
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl | rfl
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 3 hx0),
        padicValRat.pow hx0, v2_four, hva]
      omega
    · rw [padicValRat.mul (by norm_num) hx0, v2_three, hva]
      omega
    · rw [padicValRat.neg, padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divP x := by
    simp [a, L, divP]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divQ_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divQ x ≠ 0 ∧ padicValRat 2 (divQ x) = 6 * padicValRat 2 x + 1 := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := 2 * x ^ 6
  let L : List ℚ :=
    [-4 * x ^ 5, 10 * x ^ 3, -10 * x ^ 2, 4 * x, -1]
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 6 hx0)
  have hva : padicValRat 2 a = 6 * padicValRat 2 x + 1 := by
    dsimp [a]
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 6 hx0),
      padicValRat.pow hx0, v2_two]
    ring
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 5 hx0),
        padicValRat.pow hx0, v2_four, hva]
      omega
    · rw [padicValRat.mul (by norm_num) (pow_ne_zero 3 hx0),
        padicValRat.pow hx0, v2_ten, hva]
      omega
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 2 hx0),
        padicValRat.pow hx0, v2_ten, hva]
      omega
    · rw [padicValRat.mul (by norm_num) hx0, v2_four, hva]
      omega
    · rw [padicValRat.neg, padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divQ x := by
    simp [a, L, divQ]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divR_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divR x ≠ 0 ∧ padicValRat 2 (divR x) = 12 * padicValRat 2 x := by
  obtain ⟨hS0, hS⟩ := divS_v2_of_neg hx
  obtain ⟨hP0, hP⟩ := divP_v2_of_neg hx
  obtain ⟨hQ0, hQ⟩ := divQ_v2_of_neg hx
  have hleft0 : divS x ^ 2 * divQ x ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hS0) hQ0
  have hright0 : -(divP x ^ 3) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 3 hP0)
  have hleft :
      padicValRat 2 (divS x ^ 2 * divQ x) =
        12 * padicValRat 2 x + 5 := by
    rw [padicValRat.mul (pow_ne_zero 2 hS0) hQ0,
      padicValRat.pow hS0, hS, hQ]
    ring
  have hright :
      padicValRat 2 (-(divP x ^ 3)) = 12 * padicValRat 2 x := by
    rw [padicValRat.neg, padicValRat.pow hP0, hP]
    ring
  have hval : padicValRat 2 (divS x ^ 2 * divQ x + -(divP x ^ 3)) =
      padicValRat 2 (-(divP x ^ 3)) := by
    rw [add_comm]
    apply v2_add_eq_left_of_lt hright0
    rw [hleft, hright]
    omega
  have hform : divS x ^ 2 * divQ x + -(divP x ^ 3) = divR x := by
    simp [divR, sub_eq_add_neg]
  rw [hform, hright] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divPhi5_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divPhi5 x ≠ 0 ∧
      padicValRat 2 (divPhi5 x) = 25 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  obtain ⟨hS0, hS⟩ := divS_v2_of_neg hx
  obtain ⟨hP0, hP⟩ := divP_v2_of_neg hx
  obtain ⟨hQ0, hQ⟩ := divQ_v2_of_neg hx
  obtain ⟨hR0, hR⟩ := divR_v2_of_neg hx
  have hQsq :
      padicValRat 2 (divQ x ^ 2) = 12 * padicValRat 2 x + 2 := by
    rw [padicValRat.pow hQ0, hQ]
    ring
  have hdiff0 : divR x - divQ x ^ 2 ≠ 0 := by
    intro hzero
    have heq : divR x = divQ x ^ 2 := sub_eq_zero.mp hzero
    have hvals := congrArg (padicValRat 2) heq
    rw [hR, hQsq] at hvals
    omega
  have hdiff :
      padicValRat 2 (divR x - divQ x ^ 2) =
        12 * padicValRat 2 x := by
    rw [sub_eq_add_neg]
    rw [v2_add_eq_left_of_lt hR0, hR]
    rw [padicValRat.neg, hQsq, hR]
    omega
  have hfirst0 : x * divR x ^ 2 ≠ 0 :=
    mul_ne_zero hx0 (pow_ne_zero 2 hR0)
  have hsecond0 :
      -(divP x * divS x * divQ x * (divR x - divQ x ^ 2)) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hP0 hS0) hQ0) hdiff0)
  have hfirst :
      padicValRat 2 (x * divR x ^ 2) = 25 * padicValRat 2 x := by
    rw [padicValRat.mul hx0 (pow_ne_zero 2 hR0),
      padicValRat.pow hR0, hR]
    ring
  have hsecond : padicValRat 2
      (-(divP x * divS x * divQ x * (divR x - divQ x ^ 2))) =
        25 * padicValRat 2 x + 3 := by
    rw [padicValRat.neg,
      padicValRat.mul (mul_ne_zero (mul_ne_zero hP0 hS0) hQ0) hdiff0,
      padicValRat.mul (mul_ne_zero hP0 hS0) hQ0,
      padicValRat.mul hP0 hS0, hP, hS, hQ, hdiff]
    ring
  have hval := v2_add_eq_left_of_lt hfirst0 (by
    rw [hfirst, hsecond]
    omega : padicValRat 2 (x * divR x ^ 2) <
      padicValRat 2
        (-(divP x * divS x * divQ x * (divR x - divQ x ^ 2))))
  have hform :
      x * divR x ^ 2 +
        -(divP x * divS x * divQ x * (divR x - divQ x ^ 2)) =
          divPhi5 x := by
    simp [divPhi5, sub_eq_add_neg]
  rw [hform, hfirst] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divPhi2_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divPhi2 x ≠ 0 ∧
      padicValRat 2 (divPhi2 x) = 4 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := x ^ 4
  let L : List ℚ := [-2 * x, 1]
  have ha : a ≠ 0 := pow_ne_zero 4 hx0
  have hva : padicValRat 2 a = 4 * padicValRat 2 x := by
    dsimp [a]
    rw [padicValRat.pow hx0]
    norm_num
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl
    · rw [padicValRat.neg, padicValRat.mul (by norm_num) hx0,
        v2_two, hva]
      omega
    · rw [padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divPhi2 x := by
    simp [a, L, divPhi2]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem rat_den_not_even_of_v2_nonneg
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ¬ 2 ∣ x.den := by
  intro hden
  have hcop : Nat.Coprime x.num.natAbs 2 :=
    Nat.Coprime.of_dvd_right hden x.reduced
  have hnumAbs : ¬ 2 ∣ x.num.natAbs :=
    Nat.prime_two.coprime_iff_not_dvd.mp hcop.symm
  have hnum : ¬ (2 : ℤ) ∣ x.num := by
    intro hdiv
    exact hnumAbs (Int.natCast_dvd.mp hdiv)
  have hnumVal : padicValInt 2 x.num = 0 :=
    padicValInt.eq_zero_of_not_dvd hnum
  have hdenVal : 1 ≤ padicValNat 2 x.den :=
    one_le_padicValNat_of_dvd x.den_nz hden
  rw [padicValRat_def, hnumVal] at hx
  omega

private theorem rat_den_v2_eq_zero
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    padicValRat 2 (x.den : ℚ) = 0 := by
  change padicValRat 2 ((x.den : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd
    (rat_den_not_even_of_v2_nonneg x hx)

private theorem divR_num_den_formula (x : ℚ) :
    divR x =
      (divRH x.num (x.den : ℤ) : ℤ) /
        (x.den : ℚ) ^ 12 := by
  have hdenQ : (x.den : ℚ) ≠ 0 := by positivity
  have hdehom := divRH_dehom (x.num : ℚ) (x.den : ℚ) hdenQ
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    simpa using (Rat.num_div_den x).symm
  have hcast :
      ((divRH x.num (x.den : ℤ) : ℤ) : ℚ) =
        divRH (x.num : ℚ) (x.den : ℚ) := by
    norm_num [divRH, divSH, divPH, divQH]
  calc
    divR x = divR ((x.num : ℚ) / (x.den : ℚ)) := by rw [← hxrepr]
    _ = divRH (x.num : ℚ) (x.den : ℚ) / (x.den : ℚ) ^ 12 := by
      rw [hdehom]
      field_simp
    _ = (divRH x.num (x.den : ℤ) : ℤ) / (x.den : ℚ) ^ 12 := by
      rw [hcast]

private theorem divPhi5_num_den_formula (x : ℚ) :
    divPhi5 x =
      (divPhi5H x.num (x.den : ℤ) : ℤ) /
        (x.den : ℚ) ^ 25 := by
  have hdenQ : (x.den : ℚ) ≠ 0 := by positivity
  have hdehom := divPhi5H_dehom (x.num : ℚ) (x.den : ℚ) hdenQ
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    simpa using (Rat.num_div_den x).symm
  have hcast :
      ((divPhi5H x.num (x.den : ℤ) : ℤ) : ℚ) =
        divPhi5H (x.num : ℚ) (x.den : ℚ) := by
    norm_num [divPhi5H, divRH, divSH, divPH, divQH]
  calc
    divPhi5 x = divPhi5 ((x.num : ℚ) / (x.den : ℚ)) := by rw [← hxrepr]
    _ = divPhi5H (x.num : ℚ) (x.den : ℚ) / (x.den : ℚ) ^ 25 := by
      rw [hdehom]
      field_simp
    _ = (divPhi5H x.num (x.den : ℤ) : ℤ) / (x.den : ℚ) ^ 25 := by
      rw [hcast]

private theorem integral_five_homogeneous_certificate
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    (2 : ℤ) ∣ (divRH x.num (x.den : ℤ) : ℤ) ∧
      ¬ (2 : ℤ) ∣ (divPhi5H x.num (x.den : ℤ) : ℤ) := by
  have hden : ¬ 2 ∣ x.den := rat_den_not_even_of_v2_nonneg x hx
  have hb : ((x.den : ZMod 2) : ZMod 2) ≠ 0 := by
    have hbInt : (((x.den : ℤ) : ZMod 2)) ≠ 0 := by
      intro hb0
      apply hden
      exact Int.natCast_dvd.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (x.den : ℤ) 2).mp hb0)
    simpa using hbInt
  have hcert := mod_two_five_certificate (x.num : ZMod 2) (x.den : ZMod 2) hb
  have hRmod :
      ((divRH x.num (x.den : ℤ) : ℤ) : ZMod 2) = 0 := by
    simpa [divRH, divSH, divPH, divQH] using hcert.1
  have hPhimod :
      ((divPhi5H x.num (x.den : ℤ) : ℤ) : ZMod 2) = 1 := by
    simpa [divPhi5H, divRH, divSH, divPH, divQH] using hcert.2
  constructor
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hRmod
  · intro hdiv
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdiv
    rw [hPhimod] at hzero
    norm_num at hzero

private theorem divR_zero_or_v2_pos_of_nonneg {x : ℚ}
    (hx : 0 ≤ padicValRat 2 x) :
    divR x = 0 ∨
      divR x ≠ 0 ∧ 1 ≤ padicValRat 2 (divR x) := by
  by_cases hR0 : divR x = 0
  · exact Or.inl hR0
  · right
    refine ⟨hR0, ?_⟩
    let A : ℤ := divRH x.num (x.den : ℤ)
    have hAdiv : (2 : ℤ) ∣ A :=
      (integral_five_homogeneous_certificate x hx).1
    have hA0 : A ≠ 0 := by
      intro hzero
      apply hR0
      rw [divR_num_den_formula, show (divRH x.num (x.den : ℤ) : ℤ) = A by rfl,
        hzero]
      simp
    have hAvalNat : 1 ≤ padicValNat 2 A.natAbs :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hA0)
        (Int.natCast_dvd.mp hAdiv)
    have hAval : 1 ≤ padicValRat 2 (A : ℚ) := by
      rw [padicValRat.of_int]
      exact_mod_cast hAvalNat
    have hdenVal := rat_den_v2_eq_zero x hx
    rw [divR_num_den_formula,
      show (divRH x.num (x.den : ℤ) : ℤ) = A by rfl,
      padicValRat.div (Int.cast_ne_zero.mpr hA0)
        (pow_ne_zero 12 (by positivity)),
      padicValRat.pow (by positivity), hdenVal]
    omega

private theorem divPhi5_v2_of_nonneg {x : ℚ}
    (hx : 0 ≤ padicValRat 2 x) :
    divPhi5 x ≠ 0 ∧ padicValRat 2 (divPhi5 x) = 0 := by
  let A : ℤ := divPhi5H x.num (x.den : ℤ)
  have hAnotdiv : ¬ (2 : ℤ) ∣ A :=
    (integral_five_homogeneous_certificate x hx).2
  have hA0 : A ≠ 0 := by
    intro hzero
    apply hAnotdiv
    simp [hzero]
  have hAval : padicValRat 2 (A : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hAnotdiv
  have hdenVal := rat_den_v2_eq_zero x hx
  have hformula := divPhi5_num_den_formula x
  have hPhi0 : divPhi5 x ≠ 0 := by
    rw [hformula, show (divPhi5H x.num (x.den : ℤ) : ℤ) = A by rfl]
    exact div_ne_zero (Int.cast_ne_zero.mpr hA0) (pow_ne_zero 25 (by positivity))
  refine ⟨hPhi0, ?_⟩
  rw [hformula, show (divPhi5H x.num (x.den : ℤ) : ℤ) = A by rfl,
    padicValRat.div (Int.cast_ne_zero.mpr hA0)
      (pow_ne_zero 25 (by positivity)),
    padicValRat.pow (by positivity), hAval, hdenVal]
  norm_num

private theorem psi_ne_zero_of_charZero
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hpsi2ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
          (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hpsi2deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsine : ∀ (n : ℕ), n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hpsi2ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsideg : ∀ (n : ℕ), n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree ≤ 0 + 1 :=
          Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add (Polynomial.natDegree_C _).le hpsi2deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hmk :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hmk (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsine n (by intro h; exact hm (by simp [h])))
      (hPsideg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsine _ (Nat.succ_ne_zero n))
      (hPsideg _ (Nat.succ_ne_zero n))

section

noncomputable local instance : DecidableEq ℚ := Classical.decEq ℚ

private theorem minimal_five_xrep_same
    {x y : ℚ} (h : MinimalCurveBase.Nonsingular x y) :
    KeystoneLadder.SameP1Vec
      (((5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint)).xRep)
      (KeystoneLadder.xPair minimalCurve (5 : ℤ) x) := by
  exact KeystoneLadder.xRep_nsmul_same_xPair minimalCurve
    (by norm_num) (psi_ne_zero_of_charZero minimalCurve)
    (WeierstrassCurve.Ψ₃_ne_zero minimalCurve (by norm_num)) (n := 5) h

private theorem minimal_five_cross_multiplication
    {x y x5 y5 : ℚ}
    {h : MinimalCurveBase.Nonsingular x y}
    {h5 : MinimalCurveBase.Nonsingular x5 y5}
    (heq : (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) =
      WeierstrassCurve.Affine.Point.some x5 y5 h5) :
    x5 * divR x ^ 2 = divPhi5 x := by
  have hsame := minimal_five_xrep_same h
  rw [heq] at hsame
  rcases hsame with ⟨c, hc, hvec⟩
  have hzero := congrArg (fun v : Fin 2 → ℚ ↦ v 0) hvec
  have hone := congrArg (fun v : Fin 2 → ℚ ↦ v 1) hvec
  simp [KeystoneLadder.xPair, Pi.smul_apply,
    minimalCurve_Phi_five_eval, minimalCurve_PsiSq_five_eval] at hzero hone
  calc
    x5 * divR x ^ 2 = x5 * c := by rw [hone]
    _ = c * x5 := mul_comm _ _
    _ = divPhi5 x := hzero.symm

def InFormal2 : MinimalPoint → Prop
  | WeierstrassCurve.Affine.Point.zero => True
  | WeierstrassCurve.Affine.Point.some x _ _ => padicValRat 2 x < 0

@[simp] theorem inFormal2_zero : InFormal2 (0 : MinimalPoint) := by
  rw [WeierstrassCurve.Affine.Point.zero_def]
  change True
  trivial

@[simp] theorem inFormal2_some (x y : ℚ)
    (h : MinimalCurveBase.Nonsingular x y) :
    InFormal2 (WeierstrassCurve.Affine.Point.some x y h) ↔
      padicValRat 2 x < 0 := by
  rfl

theorem five_nsmul_inFormal2 (P : MinimalPoint) :
    InFormal2 ((5 : ℕ) • P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def]
    simp
  · by_cases hx : padicValRat 2 x < 0
    · obtain ⟨hR0, hR⟩ := divR_v2_of_neg hx
      obtain ⟨hPhi0, hPhi⟩ := divPhi5_v2_of_neg hx
      cases heq : (5 : ℕ) •
          (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
      | zero => change True; trivial
      | some x5 y5 h5 =>
          rw [inFormal2_some]
          have hcross := minimal_five_cross_multiplication heq
          have hx50 : x5 ≠ 0 := by
            intro hx50
            rw [hx50, zero_mul] at hcross
            exact hPhi0 hcross.symm
          have hval := congrArg (padicValRat 2) hcross
          rw [padicValRat.mul hx50 (pow_ne_zero 2 hR0),
            padicValRat.pow hR0, hR, hPhi] at hval
          omega
    · have hxnonneg : 0 ≤ padicValRat 2 x := by omega
      obtain ⟨hPhi0, hPhi⟩ := divPhi5_v2_of_nonneg hxnonneg
      rcases divR_zero_or_v2_pos_of_nonneg hxnonneg with hRzero | ⟨hR0, hR⟩
      · cases heq : (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
        | zero => change True; trivial
        | some x5 y5 h5 =>
            exfalso
            have hcross := minimal_five_cross_multiplication heq
            rw [hRzero] at hcross
            norm_num at hcross
            exact hPhi0 hcross.symm
      · cases heq : (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
        | zero => change True; trivial
        | some x5 y5 h5 =>
            rw [inFormal2_some]
            have hcross := minimal_five_cross_multiplication heq
            have hx50 : x5 ≠ 0 := by
              intro hx50
              rw [hx50, zero_mul] at hcross
              exact hPhi0 hcross.symm
            have hval := congrArg (padicValRat 2) hcross
            rw [padicValRat.mul hx50 (pow_ne_zero 2 hR0),
              padicValRat.pow hR0, hPhi] at hval
            omega

private theorem minimal_two_xrep_same
    {x y : ℚ} (h : MinimalCurveBase.Nonsingular x y) :
    KeystoneLadder.SameP1Vec
      (((2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint)).xRep)
      (KeystoneLadder.xPair minimalCurve (2 : ℤ) x) := by
  exact KeystoneLadder.xRep_nsmul_same_xPair minimalCurve
    (by norm_num) (psi_ne_zero_of_charZero minimalCurve)
    (WeierstrassCurve.Ψ₃_ne_zero minimalCurve (by norm_num)) (n := 2) h

private theorem minimal_two_cross_multiplication
    {x y x2 y2 : ℚ}
    {h : MinimalCurveBase.Nonsingular x y}
    {h2 : MinimalCurveBase.Nonsingular x2 y2}
    (heq : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) =
      WeierstrassCurve.Affine.Point.some x2 y2 h2) :
    x2 * divS x = divPhi2 x := by
  have hsame := minimal_two_xrep_same h
  rw [heq] at hsame
  rcases hsame with ⟨c, hc, hvec⟩
  have hzero := congrArg (fun v : Fin 2 → ℚ ↦ v 0) hvec
  have hone := congrArg (fun v : Fin 2 → ℚ ↦ v 1) hvec
  simp [KeystoneLadder.xPair, Pi.smul_apply] at hzero hone
  have hzero' : divPhi2 x = c * x2 := by
    calc
      divPhi2 x = x ^ 4 - minimalCurve.b₄ * x ^ 2 -
          2 * minimalCurve.b₆ * x - minimalCurve.b₈ := by
        simp [divPhi2, minimalCurve, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      _ = c * x2 := hzero
  have hone' : divS x = c := by
    calc
      divS x = minimalCurve.Ψ₂Sq.eval x :=
        (by simpa using (minimalCurve_PsiSq_two_eval x).symm)
      _ = c := hone
  calc
    x2 * divS x = x2 * c := by rw [hone']
    _ = c * x2 := mul_comm _ _
    _ = divPhi2 x := hzero'.symm

private theorem double_formal_coordinates
    {x y : ℚ} {h : MinimalCurveBase.Nonsingular x y}
    (hx : padicValRat 2 x < 0) :
    ∃ x2 y2 : ℚ, ∃ h2 : MinimalCurveBase.Nonsingular x2 y2,
      (2 : ℕ) •
          (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) =
        WeierstrassCurve.Affine.Point.some x2 y2 h2 ∧
      padicValRat 2 x2 = padicValRat 2 x - 2 := by
  obtain ⟨hS0, hS⟩ := divS_v2_of_neg hx
  obtain ⟨hPhi0, hPhi⟩ := divPhi2_v2_of_neg hx
  cases heq : (2 : ℕ) •
      (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
  | zero =>
      have hsame := minimal_two_xrep_same h
      rw [heq] at hsame
      have hsecond :=
        KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty (by
          simpa only [← WeierstrassCurve.Affine.Point.zero_def,
            WeierstrassCurve.Affine.Point.xRep_zero] using hsame)
      have hSzero : divS x = 0 := by
        have hraw : minimalCurve.Ψ₂Sq.eval x = 0 := by
          simpa [KeystoneLadder.xPair] using hsecond
        rw [← minimalCurve_PsiSq_two_eval]
        simpa using hraw
      exact (hS0 hSzero).elim
  | some x2 y2 h2 =>
      refine ⟨x2, y2, h2, ?_, ?_⟩
      · simpa only using heq
      · have hcross := minimal_two_cross_multiplication
          (x := x) (y := y) (x2 := x2) (y2 := y2) (by
            simpa only using heq)
        have hx20 : x2 ≠ 0 := by
          intro hx20
          rw [hx20, zero_mul] at hcross
          exact hPhi0 hcross.symm
        have hval := congrArg (padicValRat 2) hcross
        rw [padicValRat.mul hx20 hS0, hS, hPhi] at hval
        omega

def FormalVal (P : MinimalPoint) (k : ℤ) : Prop :=
  ∃ x y : ℚ, ∃ h : MinimalCurveBase.Nonsingular x y,
    P = WeierstrassCurve.Affine.Point.some x y h ∧
      padicValRat 2 x = k ∧ k < 0

private theorem formalVal_two {P : MinimalPoint} {k : ℤ}
    (hP : FormalVal P k) : FormalVal ((2 : ℕ) • P) (k - 2) := by
  obtain ⟨x, y, h, rfl, hx, hk⟩ := hP
  obtain ⟨x2, y2, h2, hdouble, hx2⟩ :=
    double_formal_coordinates (hx ▸ hk)
  refine ⟨x2, y2, h2, hdouble, ?_, by omega⟩
  omega

private theorem formalVal_two_pow {P : MinimalPoint} {k : ℤ}
    (hP : FormalVal P k) (n : ℕ) :
    FormalVal ((2 ^ n : ℕ) • P) (k - 2 * (n : ℤ)) := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
      have htwo := formalVal_two ih
      convert htwo using 1
      · calc
          (2 ^ (n + 1) : ℕ) • P = (2 ^ n * 2 : ℕ) • P := by
            rw [pow_succ]
          _ = (2 : ℕ) • ((2 ^ n : ℕ) • P) :=
            mul_nsmul P (2 ^ n) 2
      · push_cast
        ring

def InfinitelyTwoDivisible (P : MinimalPoint) : Prop :=
  ∀ n : ℕ, ∃ Q : MinimalPoint, (2 ^ n : ℕ) • Q = P

theorem five_nsmul_eq_zero_of_infinitelyTwoDivisible
    {P : MinimalPoint} (hdiv : InfinitelyTwoDivisible P) :
    (5 : ℕ) • P = 0 := by
  by_contra hne
  let R : MinimalPoint := (5 : ℕ) • P
  have hRne : R ≠ 0 := hne
  cases hReq : R with
  | zero =>
      apply hRne
      simpa [WeierstrassCurve.Affine.Point.zero_def] using hReq
  | some xr yr hr =>
      let n : ℕ := (padicValRat 2 xr).natAbs + 1
      obtain ⟨Q, hQ⟩ := hdiv n
      let S : MinimalPoint := (5 : ℕ) • Q
      have hrel : (2 ^ n : ℕ) • S = R := by
        dsimp [S, R]
        calc
          (2 ^ n : ℕ) • ((5 : ℕ) • Q) = (5 * 2 ^ n : ℕ) • Q :=
            (mul_nsmul Q 5 (2 ^ n)).symm
          _ = (2 ^ n * 5 : ℕ) • Q := by rw [Nat.mul_comm]
          _ = (5 : ℕ) • ((2 ^ n : ℕ) • Q) :=
            mul_nsmul Q (2 ^ n) 5
          _ = (5 : ℕ) • P := by rw [hQ]
      have hformal : InFormal2 S := five_nsmul_inFormal2 Q
      cases hSeq : S with
      | zero =>
          have hSzero : S = (0 : MinimalPoint) := by
            simpa [WeierstrassCurve.Affine.Point.zero_def] using hSeq
          apply hRne
          rw [← hrel, hSzero]
          simp
      | some xs ys hs =>
          have hxs : padicValRat 2 xs < 0 := by
            rw [hSeq] at hformal
            exact hformal
          have hFV : FormalVal S (padicValRat 2 xs) :=
            ⟨xs, ys, hs, hSeq, rfl, hxs⟩
          have hiter := formalVal_two_pow hFV n
          rw [hrel] at hiter
          obtain ⟨xt, yt, ht, hpoint, hval, _⟩ := hiter
          have hxeq : xr = xt := by
            have heqPoints :
                (WeierstrassCurve.Affine.Point.some xr yr hr : MinimalPoint) =
                  WeierstrassCurve.Affine.Point.some xt yt ht :=
              hReq.symm.trans hpoint
            rw [WeierstrassCurve.Affine.Point.some.injEq] at heqPoints
            exact heqPoints.1
          rw [← hxeq] at hval
          dsimp [n] at hval
          push_cast at hval
          by_cases hV : 0 ≤ padicValRat 2 xr
          · rw [abs_of_nonneg hV] at hval
            omega
          · have hVneg : padicValRat 2 xr < 0 := lt_of_not_ge hV
            rw [abs_of_neg hVneg] at hval
            omega

def divQ10 {R : Type*} [CommRing R] (x : R) : R :=
  5 * x ^ 10 - 15 * x ^ 9 + x ^ 8 + 96 * x ^ 7 -
    189 * x ^ 6 + 171 * x ^ 5 - 84 * x ^ 4 + 10 * x ^ 3 +
    25 * x ^ 2 - 20 * x + 5

def divQ10H {R : Type*} [CommRing R] (a b : R) : R :=
  5 * a ^ 10 - 15 * a ^ 9 * b + a ^ 8 * b ^ 2 +
    96 * a ^ 7 * b ^ 3 - 189 * a ^ 6 * b ^ 4 +
    171 * a ^ 5 * b ^ 5 - 84 * a ^ 4 * b ^ 6 +
    10 * a ^ 3 * b ^ 7 + 25 * a ^ 2 * b ^ 8 -
    20 * a * b ^ 9 + 5 * b ^ 10

private theorem divQ10H_dehom (a b : ℚ) (hb : b ≠ 0) :
    divQ10H a b = b ^ 10 * divQ10 (a / b) := by
  unfold divQ10H divQ10
  field_simp [hb]

private theorem mod_two_q10_certificate :
    ∀ a b : ZMod 2, (a ≠ 0 ∨ b ≠ 0) → divQ10H a b = 1 := by
  decide

private theorem divQ10_ne_zero (x : ℚ) : divQ10 x ≠ 0 := by
  have hpair : (x.num : ZMod 2) ≠ 0 ∨ (x.den : ZMod 2) ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    have hnumInt : (2 : ℤ) ∣ x.num :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 2).mp hnot.1
    have hdenInt : (2 : ℤ) ∣ (x.den : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x.den : ℤ) 2).mp (by
        simpa using hnot.2)
    have hnum : 2 ∣ x.num.natAbs := Int.natCast_dvd.mp hnumInt
    have hden : 2 ∣ x.den := Int.natCast_dvd.mp hdenInt
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hnum hden) x.reduced
  have hcert := mod_two_q10_certificate (x.num : ZMod 2) (x.den : ZMod 2) hpair
  let A : ℤ := divQ10H x.num (x.den : ℤ)
  have hAmod : (A : ZMod 2) = 1 := by
    simpa [A, divQ10H] using hcert
  have hA0 : A ≠ 0 := by
    intro hzero
    rw [hzero] at hAmod
    norm_num at hAmod
  intro hQzero
  have hdenQ : (x.den : ℚ) ≠ 0 := by positivity
  have hdehom := divQ10H_dehom (x.num : ℚ) (x.den : ℚ) hdenQ
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    simpa using (Rat.num_div_den x).symm
  rw [← hxrepr, hQzero, mul_zero] at hdehom
  have hcast :
      (A : ℚ) = divQ10H (x.num : ℚ) (x.den : ℚ) := by
    norm_num [A, divQ10H]
  rw [← hcast] at hdehom
  exact hA0 (Int.cast_eq_zero.mp hdehom)

private theorem divR_factor (x : ℚ) :
    divR x = x * (x - 1) * divQ10 x := by
  unfold divR divS divP divQ divQ10
  ring

theorem x_eq_zero_or_one_of_five_nsmul_eq_zero
    {x y : ℚ} {h : MinimalCurveBase.Nonsingular x y}
    (hfive : (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) = 0) :
    x = 0 ∨ x = 1 := by
  have hsame := minimal_five_xrep_same h
  rw [hfive] at hsame
  have hsecond :=
    KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty (by
      simpa [WeierstrassCurve.Affine.Point.xRep_zero] using hsame)
  have hRsq : divR x ^ 2 = 0 := by
    simpa [KeystoneLadder.xPair, minimalCurve_PsiSq_five_eval] using hsecond
  have hR : divR x = 0 := sq_eq_zero_iff.mp hRsq
  rw [divR_factor] at hR
  rcases mul_eq_zero.mp hR with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · exact (divQ10_ne_zero x h).elim

private theorem mordellToMinimalPointAddEquiv_some
    {xi eta : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208) :
    ∃ hmin : MinimalCurveBase.Nonsingular
        ((xi + 12) / 36) ((eta - 108) / 216),
      mordellToMinimalPointAddEquiv (mordellPoint xi eta hcurve) =
        WeierstrassCurve.Affine.Point.some
          ((xi + 12) / 36) ((eta - 108) / 216) hmin := by
  let X : ℚ := variableChangePointX mordellToMinimalChange xi
  let Y : ℚ := variableChangePointY mordellToMinimalChange xi eta
  let hsource : WeierstrassCurve.Affine.Nonsingular mordellCurve xi eta :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((mordellCurve_equation_iff xi eta).2 hcurve)
  let hchanged : WeierstrassCurve.Affine.Nonsingular
      (mordellToMinimalChange • mordellCurve) X Y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (variableChangePoint_equation mordellCurve mordellToMinimalChange
        hsource.left)
  obtain ⟨hminimal, hfirst⟩ :=
    pointCurveEqAddEquiv_some mordellToMinimalChange_smul hchanged
  obtain ⟨hbase, hsecond⟩ :=
    affinePointCurveEqAddEquiv_some minimalCurveBase_eq.symm hminimal
  have hX : X = (xi + 12) / 36 := by
    norm_num [X, variableChangePointX, mordellToMinimalChange]
    ring
  have hY : Y = (eta - 108) / 216 := by
    norm_num [Y, variableChangePointY, mordellToMinimalChange]
    ring
  let hmin : MinimalCurveBase.Nonsingular
      ((xi + 12) / 36) ((eta - 108) / 216) := hX ▸ hY ▸ hbase
  refine ⟨hmin, ?_⟩
  change affinePointCurveEqAddEquiv minimalCurveBase_eq.symm
      (pointCurveEqAddEquiv mordellToMinimalChange_smul
        (Scratch.TateZ2xZ10Reduction.variableChangePointMap
          mordellCurve mordellToMinimalChange (mordellPoint xi eta hcurve))) = _
  have hmap :
      Scratch.TateZ2xZ10Reduction.variableChangePointMap
          mordellCurve mordellToMinimalChange (mordellPoint xi eta hcurve) =
        WeierstrassCurve.Affine.Point.some X Y hchanged := by
    rfl
  rw [hmap, hfirst, hsecond]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

private theorem every_mordell_point_has_half
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    (P : WeierstrassCurve.Affine.Point mordellCurve) :
    ∃ Q : WeierstrassCurve.Affine.Point mordellCurve,
      (2 : ℕ) • Q = P := by
  cases P with
  | zero =>
      refine ⟨0, ?_⟩
      simpa only [← WeierstrassCurve.Affine.Point.zero_def] using
        (nsmul_zero 2 : (2 : ℕ) •
          (0 : WeierstrassCurve.Affine.Point mordellCurve) = 0)
  | some xi eta h =>
      have hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208 :=
        (mordellCurve_equation_iff xi eta).1 h.left
      obtain ⟨Q, hQ⟩ :=
        exists_mordell_half_of_factor_square hcurve (hall hcurve)
      refine ⟨Q, ?_⟩
      simpa [mordellPoint] using hQ

private theorem every_minimal_point_has_half
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    (P : MinimalPoint) :
    ∃ Q : MinimalPoint, (2 : ℕ) • Q = P := by
  let F := mordellToMinimalPointAddEquiv
  obtain ⟨R, hR⟩ := every_mordell_point_has_half hall (F.symm P)
  refine ⟨F R, ?_⟩
  calc
    (2 : ℕ) • F R = F ((2 : ℕ) • R) := (map_nsmul F 2 R).symm
    _ = F (F.symm P) := by rw [hR]
    _ = P := F.apply_symm_apply P

private theorem infinitelyTwoDivisible_of_all_factor_square
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    (P : MinimalPoint) : InfinitelyTwoDivisible P := by
  intro n
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨R, hR⟩ := ih
      obtain ⟨Q, hQ⟩ := every_minimal_point_has_half hall R
      refine ⟨Q, ?_⟩
      calc
        (2 ^ (n + 1) : ℕ) • Q = (2 * 2 ^ n : ℕ) • Q := by
          rw [pow_succ, Nat.mul_comm]
        _ = (2 ^ n : ℕ) • ((2 : ℕ) • Q) := mul_nsmul Q 2 (2 ^ n)
        _ = (2 ^ n : ℕ) • R := by rw [hQ]
        _ = P := hR

/-- If every Billing--Mahler cubic factor is a square, 2-adic separatedness
and the fifth division polynomial force every affine point to be a cusp. -/
theorem mordell_x_boundary_of_all_factor_square
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    {xi eta : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208) :
    xi = -12 ∨ xi = 24 := by
  let P : WeierstrassCurve.Affine.Point mordellCurve :=
    mordellPoint xi eta hcurve
  let F := mordellToMinimalPointAddEquiv
  have hdiv : InfinitelyTwoDivisible (F P) :=
    infinitelyTwoDivisible_of_all_factor_square hall (F P)
  have hfive : (5 : ℕ) • F P = 0 :=
    five_nsmul_eq_zero_of_infinitelyTwoDivisible hdiv
  obtain ⟨hmin, hmap⟩ := mordellToMinimalPointAddEquiv_some hcurve
  have hfive' : (5 : ℕ) •
      (WeierstrassCurve.Affine.Point.some
        ((xi + 12) / 36) ((eta - 108) / 216) hmin : MinimalPoint) = 0 := by
    simpa only [P, F, hmap] using hfive
  have hX := x_eq_zero_or_one_of_five_nsmul_eq_zero hfive'
  rcases hX with hX | hX
  · left
    linarith
  · right
    linarith

end

noncomputable def alphaInteger : OK :=
  ⟨BillingMahlerField.alpha, BillingMahlerField.alpha_isIntegral⟩

@[simp] theorem alphaInteger_coe_K : (alphaInteger : K) = BillingMahlerField.alpha := by
  rfl

private theorem ofCoords_mul_basis_zero (a b c : ℚ) :
    BillingMahlerField.ofCoords a b c * BillingMahlerField.basis (0 : Fin 3) =
      BillingMahlerField.ofCoords a b c := by
  simp [BillingMahlerField.basis_apply]

private theorem ofCoords_mul_basis_one (a b c : ℚ) :
    BillingMahlerField.ofCoords a b c * BillingMahlerField.basis (1 : Fin 3) =
      BillingMahlerField.ofCoords (2 * c) (a - 4 * c) (b + 4 * c) := by
  simp [BillingMahlerField.basis_apply]
  unfold BillingMahlerField.ofCoords
  push_cast
  ring_nf
  rw [BillingMahlerField.alpha_cubed]
  norm_num
  ring_nf

private theorem ofCoords_mul_basis_two (a b c : ℚ) :
    BillingMahlerField.ofCoords a b c * BillingMahlerField.basis (2 : Fin 3) =
      BillingMahlerField.ofCoords (2 * b + 8 * c) (-4 * b - 14 * c)
        (a + 4 * b + 12 * c) := by
  simp [BillingMahlerField.basis_apply]
  unfold BillingMahlerField.ofCoords
  push_cast
  ring_nf
  rw [BillingMahlerField.alpha_fourth, BillingMahlerField.alpha_cubed]
  norm_num
  ring_nf

theorem norm_ofCoords (a b c : ℚ) :
    Algebra.norm ℚ (BillingMahlerField.ofCoords a b c) =
      a ^ 3 + 4 * a ^ 2 * b + 8 * a ^ 2 * c + 4 * a * b ^ 2 +
        10 * a * b * c + 2 * b ^ 3 + 8 * b ^ 2 * c +
        8 * b * c ^ 2 + 4 * c ^ 3 := by
  rw [Algebra.norm_eq_matrix_det BillingMahlerField.basis, Matrix.det_fin_three]
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [ofCoords_mul_basis_zero, ofCoords_mul_basis_one, ofCoords_mul_basis_two]
  simp
  ring

theorem cubicPolyInt_aeval_alphaInteger :
    aeval alphaInteger BillingMahlerField.cubicPolyInt = 0 := by
  rw [BillingMahlerField.cubicPolyInt]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
  apply NumberField.RingOfIntegers.ext
  simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero,
    alphaInteger_coe_K] using BillingMahlerField.alpha_relation

private theorem cubicPolyInt_monic : BillingMahlerField.cubicPolyInt.Monic := by
  unfold BillingMahlerField.cubicPolyInt
  monicity!

private theorem cubicPolyInt_irreducible :
    Irreducible BillingMahlerField.cubicPolyInt := by
  apply (cubicPolyInt_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mpr
  simpa only [BillingMahlerField.cubicPoly] using
    BillingMahlerField.cubicPoly_irreducible

theorem minpoly_alphaInteger :
    minpoly ℤ alphaInteger = BillingMahlerField.cubicPolyInt := by
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd alphaInteger.isIntegral
    cubicPolyInt_aeval_alphaInteger
  have hqUnit : IsUnit q :=
    (cubicPolyInt_irreducible.isUnit_or_isUnit hq).resolve_left
      (minpoly.not_isUnit ℤ alphaInteger)
  have hassociated : Associated BillingMahlerField.cubicPolyInt (minpoly ℤ alphaInteger) := by
    rw [hq]
    simpa only [mul_one] using
      Associated.mul_left (minpoly ℤ alphaInteger)
        (associated_one_iff_isUnit.mpr hqUnit)
  exact (eq_of_monic_of_associated cubicPolyInt_monic
    (minpoly.monic alphaInteger.isIntegral) hassociated).symm

theorem adjoin_alphaInteger_eq_top : Algebra.adjoin ℤ ({alphaInteger} : Set OK) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  let A := Algebra.adjoin ℤ ({alphaInteger} : Set OK)
  have hα : alphaInteger ∈ A :=
    Algebra.subset_adjoin (R := ℤ) (Set.mem_singleton alphaInteger)
  have hbasis : ∀ i : Fin 3, BillingMahlerField.integralPowerBasis i ∈ A := by
    intro i
    fin_cases i
    · have hEq : BillingMahlerField.basisInteger (0 : Fin 3) = 1 := by
        apply NumberField.RingOfIntegers.ext
        change BillingMahlerField.basis (0 : Fin 3) = (1 : K)
        simp [BillingMahlerField.basis_apply]
      change BillingMahlerField.integralPowerBasis (0 : Fin 3) ∈ A
      rw [BillingMahlerField.integralPowerBasis_apply, hEq]
      exact A.one_mem
    · have hEq : BillingMahlerField.basisInteger (1 : Fin 3) = alphaInteger := by
        apply NumberField.RingOfIntegers.ext
        change BillingMahlerField.basis (1 : Fin 3) = BillingMahlerField.alpha
        simp [BillingMahlerField.basis_apply]
      change BillingMahlerField.integralPowerBasis (1 : Fin 3) ∈ A
      rw [BillingMahlerField.integralPowerBasis_apply, hEq]
      exact hα
    · have hEq : BillingMahlerField.basisInteger (2 : Fin 3) = alphaInteger ^ 2 := by
        apply NumberField.RingOfIntegers.ext
        change BillingMahlerField.basis (2 : Fin 3) = BillingMahlerField.alpha ^ 2
        simp [BillingMahlerField.basis_apply]
      change BillingMahlerField.integralPowerBasis (2 : Fin 3) ∈ A
      rw [BillingMahlerField.integralPowerBasis_apply, hEq]
      exact A.pow_mem hα 2
  rw [← BillingMahlerField.integralPowerBasis.sum_repr u]
  exact Submodule.sum_mem A.toSubmodule fun i _ ↦
    A.smul_mem (hbasis i) (BillingMahlerField.integralPowerBasis.repr u i)

theorem exponent_alphaInteger_eq_one :
    RingOfIntegers.exponent alphaInteger = 1 := by
  exact RingOfIntegers.exponent_eq_one_iff.mpr adjoin_alphaInteger_eq_top

private theorem basisInteger_zero :
    BillingMahlerField.basisInteger (0 : Fin 3) = 1 := by
  apply NumberField.RingOfIntegers.ext
  change BillingMahlerField.basis (0 : Fin 3) = (1 : K)
  simp [BillingMahlerField.basis_apply]

private theorem basisInteger_one :
    BillingMahlerField.basisInteger (1 : Fin 3) = alphaInteger := by
  apply NumberField.RingOfIntegers.ext
  change BillingMahlerField.basis (1 : Fin 3) = BillingMahlerField.alpha
  simp [BillingMahlerField.basis_apply]

noncomputable def intPolynomial (a b c : ℤ) : OK :=
  algebraMap ℤ OK a + algebraMap ℤ OK b * alphaInteger +
    algebraMap ℤ OK c * alphaInteger ^ 2

theorem descentInteger_eq_intPolynomial (x z : ℤ) :
    BillingMahlerField.descentInteger x z =
      algebraMap ℤ OK (x - 24 * z ^ 2) +
        algebraMap ℤ OK (18 * z ^ 2) * alphaInteger := by
  apply NumberField.RingOfIntegers.ext
  rw [BillingMahlerField.descentInteger_coe_K]
  simp [BillingMahlerField.descentElement, BillingMahlerField.ofCoords,
    BillingMahlerField.basis_apply]
  norm_num [map_ofNat]

theorem exists_intPolynomial_coords (u : OK) :
    ∃ a b c : ℤ, u = intPolynomial a b c := by
  obtain ⟨a, b, c, hu⟩ := BillingMahlerField.ringOfIntegers_exists_integer_coords u
  refine ⟨a, b, c, ?_⟩
  unfold intPolynomial
  apply NumberField.RingOfIntegers.ext
  change (u : K) =
    algebraMap ℤ K a + algebraMap ℤ K b * BillingMahlerField.alpha +
      algebraMap ℤ K c * BillingMahlerField.alpha ^ 2
  simpa [BillingMahlerField.ofCoords] using hu

theorem absNorm_descentInteger_span
    (x z y : ℤ)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    Ideal.absNorm (Ideal.span ({BillingMahlerField.descentInteger x z} : Set OK)) =
      y.natAbs ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have hnorm : Algebra.norm ℤ (BillingMahlerField.descentInteger x z) = y ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, BillingMahlerField.descentInteger_coe_K,
      BillingMahlerField.norm_descentElement, ← hmodel]
  rw [hnorm, Int.natAbs_pow]

private theorem prime_not_dvd_eighteen {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ (p : ℤ) ∣ 18 := by
  intro h
  have hnat : p ∣ 18 := by exact_mod_cast h
  have hle : p ≤ 18 := Nat.le_of_dvd (by norm_num) hnat
  interval_cases p <;> norm_num at *

noncomputable def descentResidue (p : ℕ) [Fact p.Prime] (x z : ℤ) :
    ResidueInt p :=
  -(algebraMap ℤ (ResidueInt p) (x - 24 * z ^ 2)) /
    algebraMap ℤ (ResidueInt p) (18 * z ^ 2)

noncomputable def residueEval (p : ℕ) [Fact p.Prime]
    (x z a b c : ℤ) : ResidueInt p :=
  algebraMap ℤ (ResidueInt p) a +
    algebraMap ℤ (ResidueInt p) b * descentResidue p x z +
    algebraMap ℤ (ResidueInt p) c * descentResidue p x z ^ 2

private theorem mem_intPolynomial_iff_residueEval_eq_zero
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (x z a b c : ℤ)
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (halpha : Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z)) :
    intPolynomial a b c ∈ P ↔ residueEval p x z a b c = 0 := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  have hmap (n : ℤ) :
      Ideal.Quotient.mk P (algebraMap ℤ OK n) =
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) n) := by
    change algebraMap ℤ (OK ⧸ P) n = _
    exact IsScalarTower.algebraMap_apply ℤ (ResidueInt p) (OK ⧸ P) n
  have heval :
      Ideal.Quotient.mk P (intPolynomial a b c) =
        algebraMap (ResidueInt p) (OK ⧸ P) (residueEval p x z a b c) := by
    simp only [intPolynomial, residueEval, map_add, map_mul, map_pow, hmap, halpha]
  rw [← Ideal.Quotient.eq_zero_iff_mem, heval]
  constructor
  · intro h
    apply FaithfulSMul.algebraMap_injective (ResidueInt p) (OK ⧸ P)
    simpa using h
  · intro h
    rw [h]
    exact map_zero _

private theorem inertiaDeg_eq_one_of_alpha_eq_descentResidue
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (x z : ℤ) (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (halpha : Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z)) :
    (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P = 1 := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  rw [Ideal.inertiaDeg_algebraMap]
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨FaithfulSMul.algebraMap_injective (ResidueInt p) (OK ⧸ P), ?_⟩
  have hmap (n : ℤ) :
      Ideal.Quotient.mk P (algebraMap ℤ OK n) =
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) n) := by
    change algebraMap ℤ (OK ⧸ P) n = _
    exact IsScalarTower.algebraMap_apply ℤ (ResidueInt p) (OK ⧸ P) n
  intro q
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, b, c, hu⟩ := exists_intPolynomial_coords u
  refine ⟨residueEval p x z a b c, ?_⟩
  rw [hu]
  simp only [intPolynomial, residueEval, map_add, map_mul, map_pow,
    halpha, hmap]

private theorem primes_eq_of_alpha_eq_descentResidue
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (x z : ℤ) (P Q : Ideal OK)
    [P.IsPrime] [NeZero P] [Q.IsPrime] [NeZero Q]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (halphaP : Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z))
    (halphaQ : Ideal.Quotient.mk Q alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ Q) (descentResidue p x z)) :
    P = Q := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a, b, c, habc⟩ := exists_intPolynomial_coords u
    rw [habc] at hu ⊢
    exact (mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c Q halphaQ).mpr
      ((mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c P halphaP).mp hu)
  · intro u hu
    obtain ⟨a, b, c, habc⟩ := exists_intPolynomial_coords u
    rw [habc] at hu ⊢
    exact (mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c P halphaP).mpr
      ((mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c Q halphaQ).mp hu)

private theorem descentResidue_two_eq_zero (x z : ℤ) :
    descentResidue 2 x z = 0 := by
  have hden : algebraMap ℤ (ResidueInt 2) (18 * z ^ 2) = 0 := by
    change Ideal.Quotient.mk (Ideal.span ({(2 : ℤ)} : Set ℤ)) (18 * z ^ 2) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨9 * z ^ 2, by ring⟩
  rw [descentResidue, hden, div_zero]

private theorem alpha_mem_prime_above_two
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))] :
    alphaInteger ∈ P := by
  have h2under : (2 : ℤ) ∈ P.under ℤ := by
    rw [← P.over_def (Ideal.span ({(2 : ℤ)} : Set ℤ))]
    exact Ideal.mem_span_singleton_self 2
  have h2P : algebraMap ℤ OK 2 ∈ P := by
    rw [← Ideal.mem_under]
    exact h2under
  have h4P : algebraMap ℤ OK 4 ∈ P := by
    have := P.mul_mem_left (algebraMap ℤ OK 2) h2P
    norm_num [← map_mul] at this ⊢
    exact this
  have hrel : alphaInteger ^ 3 =
      algebraMap ℤ OK 4 * alphaInteger ^ 2 -
        algebraMap ℤ OK 4 * alphaInteger + algebraMap ℤ OK 2 := by
    apply NumberField.RingOfIntegers.ext
    change BillingMahlerField.alpha ^ 3 =
      algebraMap ℤ K 4 * BillingMahlerField.alpha ^ 2 -
        algebraMap ℤ K 4 * BillingMahlerField.alpha + algebraMap ℤ K 2
    norm_num [map_ofNat]
    exact BillingMahlerField.alpha_cubed
  have halpha3 : alphaInteger ^ 3 ∈ P := by
    rw [hrel]
    exact P.add_mem
      (P.sub_mem (P.mul_mem_right _ h4P) (P.mul_mem_right _ h4P)) h2P
  exact (inferInstance : P.IsPrime).mem_of_pow_mem 3 halpha3

private theorem alpha_mod_prime_above_two_eq_descentResidue
    (x z : ℤ) (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))] :
    Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt 2) (OK ⧸ P) (descentResidue 2 x z) := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  rw [descentResidue_two_eq_zero, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (alpha_mem_prime_above_two P)

private theorem cubicPoly_mod_three_irreducible :
    Irreducible
      (BillingMahlerField.cubicPolyInt.map (Int.castRingHom (ZMod 3))) := by
  let f : (ZMod 3)[X] := X ^ 3 + 2 * X ^ 2 + X + 1
  have hf : BillingMahlerField.cubicPolyInt.map (Int.castRingHom (ZMod 3)) = f := by
    simp [BillingMahlerField.cubicPolyInt, f]
    have hthree : (3 : (ZMod 3)[X]) = 0 := by
      change C (3 : ZMod 3) = 0
      rw [show (3 : ZMod 3) = 0 by decide, map_zero]
    linear_combination (-2 * X ^ 2 + X - 1) * hthree
  rw [hf]
  have hfmonic : f.Monic := by
    dsimp [f]
    monicity!
  have hfdeg : f.natDegree = 3 := by
    dsimp [f]
    compute_degree <;> norm_num
  apply (hfmonic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega) (by omega)).mpr
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro r
  rw [mem_roots hfmonic.ne_zero]
  fin_cases r
  · have hval : eval (0 : ZMod 3) f = 1 := by simp [f]
    change eval (0 : ZMod 3) f ≠ 0
    rw [hval]
    exact one_ne_zero
  · have hval : eval (1 : ZMod 3) f = 2 := by
      simp [f]
      decide
    change eval (1 : ZMod 3) f ≠ 0
    rw [hval]
    decide
  · have hval : eval (2 : ZMod 3) f = 1 := by
      simp [f]
      decide
    change eval (2 : ZMod 3) f ≠ 0
    rw [hval]
    exact one_ne_zero

private theorem span_three_isMaximal :
    (Ideal.span ({(3 : OK)} : Set OK)).IsMaximal := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let m3 : (ZMod 3)[X] :=
    (minpoly ℤ alphaInteger).map (Int.castRingHom (ZMod 3))
  have hm3 : Irreducible m3 := by
    simpa [m3, minpoly_alphaInteger] using cubicPoly_mod_three_irreducible
  letI : Fact (Irreducible m3) := ⟨hm3⟩
  have hexponent : ¬ 3 ∣ RingOfIntegers.exponent alphaInteger := by
    rw [exponent_alphaInteger_eq_one]
    norm_num
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan
    (K := K) (p := 3) (θ := alphaInteger) hexponent
  apply Ideal.Quotient.maximal_of_isField
  exact e.symm.toMulEquiv.isField (Field.toIsField _)

private theorem prime_above_three_eq_span
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))] :
    P = Ideal.span ({(3 : OK)} : Set OK) := by
  apply Eq.symm
  apply Ideal.IsMaximal.eq_of_le span_three_isMaximal
    (inferInstance : P.IsPrime).ne_top
  rw [Ideal.span_singleton_le_iff_mem]
  have h3under : (3 : ℤ) ∈ P.under ℤ := by
    rw [← P.over_def (Ideal.span ({(3 : ℤ)} : Set ℤ))]
    exact Ideal.mem_span_singleton_self 3
  change algebraMap ℤ OK 3 ∈ P
  rw [← Ideal.mem_under]
  exact h3under

private theorem inertiaDeg_prime_above_three
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))] :
    (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P = 3 := by
  have hnorm : Ideal.absNorm P = 3 ^ 3 := by
    rw [prime_above_three_eq_span P]
    calc
      Ideal.absNorm (Ideal.span ({(3 : OK)} : Set OK)) =
          3 ^ Module.finrank ℤ OK := by
        simpa using (Ideal.absNorm_span_natCast (S := OK) 3)
      _ = 3 ^ 3 := by
        rw [NumberField.RingOfIntegers.rank, BillingMahlerField.finrank_K]
  have hpow := Ideal.absNorm_eq_pow_inertiaDeg' P (by norm_num : Nat.Prime 3)
  rw [hnorm] at hpow
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow.symm

private theorem normalized_factor_count_even_of_unique_odd_inertia
    (J : Ideal OK) (hJ : J ≠ ⊥) (n : ℕ)
    (hJnorm : Ideal.absNorm J = n ^ 2)
    (P : Ideal OK) (hPmem : P ∈ normalizedFactors J)
    (hodd : Odd
      ((Ideal.span ({(Ideal.absNorm (P.under ℤ) : ℤ)} : Set ℤ)).inertiaDeg P))
    (hunique : ∀ Q : Ideal OK, Q ∈ normalizedFactors J →
      Ideal.absNorm (Q.under ℤ) = Ideal.absNorm (P.under ℤ) → Q = P) :
    Even ((normalizedFactors J).count P) := by
  let p := Ideal.absNorm (P.under ℤ)
  let k := (normalizedFactors J).count P
  have hPprime : Prime P := prime_of_normalized_factor P hPmem
  letI : P.IsPrime := Ideal.isPrime_of_prime hPprime
  letI : NeZero P := ⟨hPprime.ne_zero⟩
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  have hp : p.Prime := Nat.absNorm_under_prime P
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hPR, hdecomp⟩ := Ideal.eq_prime_pow_mul_coprime hJ P
  have hR : R ≠ ⊥ := by
    intro hR
    apply hJ
    calc
      J = P ^ (Multiset.count P (normalizedFactors J)) * R := hdecomp
      _ = ⊥ := by simp [hR]
  have hRnorm : Ideal.absNorm R ≠ 0 := by
    intro hnorm
    exact hR (Ideal.absNorm_eq_zero_iff.mp hnorm)
  have hpR : ¬ p ∣ Ideal.absNorm R := by
    intro hpR
    obtain ⟨Q, hQmax, hQunder, hQdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp R hpR
    have hJleR : J ≤ R := by
      rw [hdecomp]
      exact Ideal.mul_le_left
    have hRleQ : R ≤ Q := Ideal.dvd_iff_le.mp hQdvd
    have hQmem : Q ∈ normalizedFactors J :=
      (Ideal.mem_normalizedFactors_iff hJ).mpr
        ⟨hQmax.isPrime, hJleR.trans hRleQ⟩
    have hQnorm : Ideal.absNorm (Q.under ℤ) = p := by
      rw [hQunder]
      simp
    have hQP : Q = P := hunique Q hQmem hQnorm
    have hRleP : R ≤ P := by simpa only [hQP] using hRleQ
    rw [sup_eq_left.mpr hRleP] at hPR
    exact (inferInstance : P.IsPrime).ne_top hPR
  have hPnorm : Ideal.absNorm P =
      p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P) :=
    Ideal.absNorm_eq_pow_inertiaDeg' P hp
  have hnormDecomp : Ideal.absNorm J =
      (p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P)) ^ k *
        Ideal.absNorm R := by
    rw [hdecomp, map_mul, map_pow, hPnorm]
  have hpne : p ≠ 0 := hp.ne_zero
  have hPpowne :
      (p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P)) ^ k ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hpne)
  have hfactor : (Ideal.absNorm J).factorization p =
      k * ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P) := by
    rw [hnormDecomp, Nat.factorization_mul hPpowne hRnorm,
      Nat.factorization_pow, Nat.Prime.factorization_pow hp]
    simp [Nat.factorization_eq_zero_of_not_dvd hpR, mul_comm]
  have hfactorEven : Even ((Ideal.absNorm J).factorization p) := by
    refine ⟨n.factorization p, ?_⟩
    rw [hJnorm, Nat.factorization_pow]
    simp [two_nsmul]
  have hkMulEven : Even
      (k * ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P)) := by
    rw [← hfactor]
    exact hfactorEven
  by_contra hk
  have hkOdd : Odd k := Nat.not_even_iff_odd.mp hk
  have hprodOdd : Odd
      (k * ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P)) :=
    hkOdd.mul hodd
  exact (Nat.not_even_iff_odd.mpr hprodOdd) hkMulEven

private theorem alpha_mod_prime_eq_descentResidue
    {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (x z : ℤ) (hpz : ¬ (p : ℤ) ∣ z)
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hdelta : BillingMahlerField.descentInteger x z ∈ P) :
    Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z) := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  let A : ℤ := x - 24 * z ^ 2
  let B : ℤ := 18 * z ^ 2
  have hpB : ¬ (p : ℤ) ∣ B := by
    intro hB
    have hcases : (p : ℤ) ∣ 18 ∨ (p : ℤ) ∣ z ^ 2 :=
      (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp (by simpa [B] using hB)
    rcases hcases with h18 | hz2
    · exact prime_not_dvd_eighteen hp hp2 hp3 h18
    · exact hpz ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hz2)
  have hB0 : algebraMap ℤ (ResidueInt p) B ≠ 0 := by
    change Ideal.Quotient.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) B ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hpB
  have hzero :
      Ideal.Quotient.mk P (BillingMahlerField.descentInteger x z) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hdelta
  have hmap (n : ℤ) :
      Ideal.Quotient.mk P (algebraMap ℤ OK n) =
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) n) := by
    change algebraMap ℤ (OK ⧸ P) n = _
    exact IsScalarTower.algebraMap_apply ℤ (ResidueInt p) (OK ⧸ P) n
  have hzero' :
      algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) A) +
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) B) *
          Ideal.Quotient.mk P alphaInteger = 0 := by
    rw [descentInteger_eq_intPolynomial] at hzero
    change Ideal.Quotient.mk P (algebraMap ℤ OK A) +
        Ideal.Quotient.mk P (algebraMap ℤ OK B) *
          Ideal.Quotient.mk P alphaInteger = 0 at hzero
    rw [hmap A, hmap B] at hzero
    exact hzero
  have hBE :
      algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) B) ≠ 0 :=
    by
      intro h
      apply hB0
      apply FaithfulSMul.algebraMap_injective (ResidueInt p) (OK ⧸ P)
      simpa using h
  change Ideal.Quotient.mk P alphaInteger =
    algebraMap (ResidueInt p) (OK ⧸ P)
      (-(algebraMap ℤ (ResidueInt p) A) /
        algebraMap ℤ (ResidueInt p) B)
  rw [map_div₀ (algebraMap (ResidueInt p) (OK ⧸ P)), map_neg,
    eq_div_iff hBE]
  linear_combination hzero'

private theorem prime_below_not_dvd_z
    (x z : ℤ) (hcop : Int.gcd x z = 1)
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    (hdelta : BillingMahlerField.descentInteger x z ∈ P) :
    ¬ (Ideal.absNorm (P.under ℤ) : ℤ) ∣ z := by
  intro hpz
  let p := Ideal.absNorm (P.under ℤ)
  have hzP : algebraMap ℤ OK z ∈ P :=
    (Int.cast_mem_ideal_iff (I := P)).mpr hpz
  have hz2P : algebraMap ℤ OK (z ^ 2) ∈ P := by
    simpa only [map_pow] using P.pow_mem_of_mem hzP 2 (by norm_num)
  have h24P : algebraMap ℤ OK (24 * z ^ 2) ∈ P := by
    rw [map_mul]
    exact P.mul_mem_left _ hz2P
  have h18P : algebraMap ℤ OK (18 * z ^ 2) * alphaInteger ∈ P := by
    rw [map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hz2P)
  have hxP : algebraMap ℤ OK x ∈ P := by
    rw [descentInteger_eq_intPolynomial] at hdelta
    have heq : algebraMap ℤ OK x =
        (algebraMap ℤ OK (x - 24 * z ^ 2) +
          algebraMap ℤ OK (18 * z ^ 2) * alphaInteger) +
          algebraMap ℤ OK (24 * z ^ 2) -
          algebraMap ℤ OK (18 * z ^ 2) * alphaInteger := by
      push_cast
      ring
    rw [heq]
    exact P.sub_mem (P.add_mem hdelta h24P) h18P
  have hpx : (p : ℤ) ∣ x := (Int.cast_mem_ideal_iff (I := P)).mp hxP
  have hp : p.Prime := Nat.absNorm_under_prime P
  have hcop' : IsCoprime x z := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  exact (Nat.prime_iff_prime_int.mp hp).not_unit
    (hcop'.isUnit_of_dvd' hpx hpz)

private theorem ideal_square_of_even_factor_counts
    (J : Ideal OK) (hJ : J ≠ ⊥)
    (heven : ∀ P : Ideal OK, Even ((normalizedFactors J).count P)) :
    ∃ I : Ideal OK, J = I ^ 2 := by
  classical
  obtain ⟨M, hM⟩ := Multiset.exists_smul_of_dvd_count (normalizedFactors J)
    (k := 2) (fun P hP ↦ (heven P).two_dvd)
  refine ⟨M.prod, ?_⟩
  calc
    J = (normalizedFactors J).prod := (Ideal.prod_normalizedFactors_eq_self hJ).symm
    _ = (2 • M).prod := by rw [hM]
    _ = M.prod ^ 2 := Multiset.prod_nsmul M 2

/-- The principal ideal generated by the Billing--Mahler cubic factor is an
ideal square for every nonzero primitive solution of the Mordell model. -/
theorem descentInteger_span_eq_sq
    (x z y : ℤ) (hcop : Int.gcd x z = 1) (hy : y ≠ 0)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    ∃ I : Ideal OK,
      Ideal.span ({BillingMahlerField.descentInteger x z} : Set OK) = I ^ 2 := by
  classical
  let J : Ideal OK :=
    Ideal.span ({BillingMahlerField.descentInteger x z} : Set OK)
  have hJnorm : Ideal.absNorm J = y.natAbs ^ 2 := by
    exact absNorm_descentInteger_span x z y hmodel
  have hynat : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
  have hJ : J ≠ ⊥ := by
    intro hbot
    have hzero : y.natAbs ^ 2 = 0 := by
      rw [← hJnorm, hbot]
      simp
    exact (pow_ne_zero 2 hynat) hzero
  apply ideal_square_of_even_factor_counts J hJ
  intro P
  by_cases hPmem : P ∈ normalizedFactors J
  · let p := Ideal.absNorm (P.under ℤ)
    have hPprime : Prime P := prime_of_normalized_factor P hPmem
    letI : P.IsPrime := Ideal.isPrime_of_prime hPprime
    letI : NeZero P := ⟨hPprime.ne_zero⟩
    have hp : p.Prime := Nat.absNorm_under_prime P
    letI : Fact p.Prime := ⟨hp⟩
    letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      dsimp [p]
      infer_instance
    have hdelta : BillingMahlerField.descentInteger x z ∈ P := by
      have hJleP := (Ideal.mem_normalizedFactors_iff hJ).mp hPmem |>.2
      exact hJleP (Ideal.subset_span (Set.mem_singleton _))
    have hpz : ¬ (p : ℤ) ∣ z := by
      simpa only [p] using prime_below_not_dvd_z x z hcop P hdelta
    have hodd : Odd
        ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P) := by
      rcases eq_or_ne p 2 with hp2 | hp2
      · letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
          simpa [hp2] using
            (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
        have halpha := alpha_mod_prime_above_two_eq_descentResidue x z P
        have hinertia :
            (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P = 1 := by
          simpa [hp2] using
            inertiaDeg_eq_one_of_alpha_eq_descentResidue (by norm_num) x z P halpha
        rw [hinertia]
        exact odd_one
      · rcases eq_or_ne p 3 with hp3 | hp3
        · letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
            simpa [hp3] using
              (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
          have hinertia :
              (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg P = 3 := by
            simpa [hp3] using inertiaDeg_prime_above_three P
          rw [hinertia]
          exact ⟨1, by norm_num⟩
        · have halpha := alpha_mod_prime_eq_descentResidue
            hp hp2 hp3 x z hpz P hdelta
          rw [inertiaDeg_eq_one_of_alpha_eq_descentResidue hp x z P halpha]
          exact odd_one
    have hunique : ∀ Q : Ideal OK, Q ∈ normalizedFactors J →
        Ideal.absNorm (Q.under ℤ) = p → Q = P := by
      intro Q hQmem hQnorm
      have hQprime : Prime Q := prime_of_normalized_factor Q hQmem
      letI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
      letI : NeZero Q := ⟨hQprime.ne_zero⟩
      letI : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
        rw [← hQnorm]
        infer_instance
      rcases eq_or_ne p 2 with hp2 | hp2
      · letI : Q.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
          simpa [hp2] using
            (inferInstance : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
        letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
          simpa [hp2] using
            (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
        exact primes_eq_of_alpha_eq_descentResidue (by norm_num) x z Q P
          (alpha_mod_prime_above_two_eq_descentResidue x z Q)
          (alpha_mod_prime_above_two_eq_descentResidue x z P)
      · rcases eq_or_ne p 3 with hp3 | hp3
        · letI : Q.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
            simpa [hp3] using
              (inferInstance : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
          letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
            simpa [hp3] using
              (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
          calc
            Q = Ideal.span ({(3 : OK)} : Set OK) := prime_above_three_eq_span Q
            _ = P := (prime_above_three_eq_span P).symm
        · have hQdelta : BillingMahlerField.descentInteger x z ∈ Q := by
            have hJleQ := (Ideal.mem_normalizedFactors_iff hJ).mp hQmem |>.2
            exact hJleQ (Ideal.subset_span (Set.mem_singleton _))
          exact primes_eq_of_alpha_eq_descentResidue hp x z Q P
            (alpha_mod_prime_eq_descentResidue hp hp2 hp3 x z hpz Q hQdelta)
            (alpha_mod_prime_eq_descentResidue hp hp2 hp3 x z hpz P hdelta)
    exact normalized_factor_count_even_of_unique_odd_inertia
      J hJ y.natAbs hJnorm P hPmem (by simpa only [p] using hodd)
        (by simpa only [p] using hunique)
  · rw [Multiset.count_eq_zero.mpr hPmem]
    exact ⟨0, by simp⟩

end MazurProof.RationalPointsN11IdealSquare
