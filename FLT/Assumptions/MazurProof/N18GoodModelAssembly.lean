import FLT.Assumptions.MazurProof.N18AddCongr
import FLT.Assumptions.MazurProof.N18PackageII
import FLT.Assumptions.MazurProof.N18GoodModelValCoords
import FLT.Assumptions.MazurProof.N18VpiWrapper
import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18Block5Instantiation
import FLT.Assumptions.MazurProof.CyclicExclusion18
import FLT.Assumptions.MazurProof.N18RouteC_Block7
import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSound
import FLT.Assumptions.MazurProof.N18RouteC_TorsionTable

/-!
# N18 good-model final assembly

This file records the complete dependency path from the two formal-kernel
packages on the integral good model `E0Good` to the elementary five-descent
contradiction.  The old `N18Block5Instantiation.FormalKernelData` is tied to
the original additive-at-three equation.  Consequently this file gives the
same interface on `E0GoodPoint`, where reduction at `pi` is good, and feeds it
to the already verified abstract `FormalKernel18` and separatedness machines.

Every remaining infrastructure gap is isolated as a named theorem: the good
reduction homomorphism and its kernel, one coordinate nonvanishing lemma, the
weak chart congruence, negation at the valuation level, and the fact that
three-power torsion reduces into the formal kernel.
-/

open scoped Classical NumberField WeierstrassCurve.Affine

namespace MazurProof.N18GoodModelAssembly

-- Prevent the abstract structure projection from competing with the concrete
-- elliptic-curve point group during elaboration.
attribute [-instance] _root_.FormalKernel18.addCommGroup

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.IsogenyPoints
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

set_option maxHeartbeats 0

abbrev GoodPoint := MazurProof.N18RouteC.GoodModel.E0GoodPoint

/-! ## The good formal kernel and its concrete package inputs -/

/-- The affine `x`-coordinate on the good equation, totalized by `0` at `O`. -/
def xCoordGood : GoodPoint → L
  | .zero => 0
  | .some x _ _ => x

/-- The near-origin locus on the good equation. -/
def InFormalKernel : GoodPoint → Prop :=
  fun P ↦ P = 0 ∨ ordPi (xCoordGood P) < 0

@[simp] theorem zero_mem_formalKernel : InFormalKernel (0 : GoodPoint) :=
  Or.inl rfl

/-- Negation preserves the affine `x`-coordinate. -/
theorem xCoordGood_neg (P : GoodPoint) : xCoordGood (-P) = xCoordGood P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

private theorem two_nsmul_eq_two_mul (a : WithTop ℤ) : 2 • a = 2 * a := by
  cases a with
  | top => simp [two_nsmul]
  | coe m =>
      rw [two_nsmul, ← WithTop.coe_add,
        show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) by norm_cast,
        ← WithTop.coe_mul]
      congr
      ring

private theorem nsmul_zero_good (n : ℕ) : n • (0 : GoodPoint) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ_nsmul, ih]; rfl

/-- A finite good-model point with negative `x`-order cannot have `y = 0`.
This is the monic-cubic Newton-polygon lemma used immediately before
`GoodModel.val_coords`; it has no group-law or descent content. -/
theorem yCoordGood_ne_zero_of_ordPi_x_neg {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular
      MazurProof.N18RouteC.E0Good x y)
    (hx : ordPi x < 0) : y ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hx
    omega
  intro hy
  subst y
  have heq := (WeierstrassCurve.Affine.equation_iff x 0).mp h.1
  have ha₂map :
      algebraMap MazurProof.N18PackageII.OL L
          MazurProof.N18PackageII.E0GoodInt.a₂ = E0Good.a₂ := by
    have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₂)
      MazurProof.N18PackageII.E0GoodInt_map
    simpa only [WeierstrassCurve.map_a₂] using hm
  have ha₄map :
      algebraMap MazurProof.N18PackageII.OL L
          MazurProof.N18PackageII.E0GoodInt.a₄ = E0Good.a₄ := by
    have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₄)
      MazurProof.N18PackageII.E0GoodInt_map
    simpa only [WeierstrassCurve.map_a₄] using hm
  have ha₆map :
      algebraMap MazurProof.N18PackageII.OL L
          MazurProof.N18PackageII.E0GoodInt.a₆ = E0Good.a₆ := by
    have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₆)
      MazurProof.N18PackageII.E0GoodInt_map
    simpa only [WeierstrassCurve.map_a₆] using hm
  have ha₂ : 0 ≤ ordPi E0Good.a₂ := by
    rw [← ha₂map]
    exact MazurProof.N18RouteC.GoodModel.zero_le_ordPi_ringOfIntegers _
  have ha₄ : 0 ≤ ordPi E0Good.a₄ := by
    rw [← ha₄map]
    exact MazurProof.N18RouteC.GoodModel.zero_le_ordPi_ringOfIntegers _
  have ha₆ : 0 ≤ ordPi E0Good.a₆ := by
    rw [← ha₆map]
    exact MazurProof.N18RouteC.GoodModel.zero_le_ordPi_ringOfIntegers _
  have hx2 : ordPi (x ^ 2) = 2 * ordPi x := by
    rw [show x ^ 2 = x * x by ring, ordPi_mul hx0 hx0]
    ring
  have hx3 : ordPi (x ^ 3) = 3 * ordPi x := by
    rw [show x ^ 3 = x * x * x by ring,
      ordPi_mul (mul_ne_zero hx0 hx0) hx0, ordPi_mul hx0 hx0]
    ring
  have ha₂x :
      2 * ordPi x ≤ ordPi (E0Good.a₂ * x ^ 2) := by
    by_cases hzero : E0Good.a₂ = 0
    · rw [hzero, zero_mul, ordPi_zero]
      omega
    · rw [ordPi_mul hzero (pow_ne_zero 2 hx0), hx2]
      omega
  have ha₄x :
      2 * ordPi x ≤ ordPi (E0Good.a₄ * x) := by
    by_cases hzero : E0Good.a₄ = 0
    · rw [hzero, zero_mul, ordPi_zero]
      omega
    · rw [ordPi_mul hzero hx0]
      omega
  have htail :
      2 * ordPi x ≤
        ordPi (E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    apply le_ordPi_add
    · exact le_ordPi_add ha₂x ha₄x (by omega)
    · omega
    · omega
  have hcurve :
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ = 0 := by
    norm_num at heq
    exact heq.symm
  have hfactor :
      x ^ 3 = -(E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    linear_combination hcurve
  have hord := congrArg ordPi hfactor
  rw [hx3, ordPi_neg] at hord
  omega

/-- The forward coordinate-valuation bridge on the good model. -/
theorem vpi_pos_bridge_good (P : GoodPoint)
    (hx : ordPi (xCoordGood P) < 0) :
    0 < vpiGood (MazurProof.N18PackageII.zParamGood P) := by
  cases P with
  | zero =>
      simp [xCoordGood, ordPi_zero] at hx
  | some x y h =>
      simp only [xCoordGood] at hx
      have hx0 : x ≠ 0 := by
        intro hzero
        rw [hzero, ordPi_zero] at hx
        omega
      have hy0 : y ≠ 0 := yCoordGood_ne_zero_of_ordPi_x_neg h hx
      have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
      have hcoords := MazurProof.N18RouteC.GoodModel.val_coords
        hx0 hy0 (by simpa using heq) hx
      have hz0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
      rw [MazurProof.N18PackageII.zParamGood_some,
        vpiGood_apply_of_ne hz0]
      exact_mod_cast (show 0 < ordPi (-x / y) by omega)

/-- Negation has the same formal-parameter order on the good chart.  It is the
valuation-level form of the formal inverse expansion `i(T) = -T + O(T²)`. -/
theorem vpi_zParamGood_neg (P : GoodPoint) :
    InFormalKernel P →
    vpiGood (MazurProof.N18PackageII.zParamGood (-P)) =
      vpiGood (MazurProof.N18PackageII.zParamGood P) := by
  intro hP
  rcases hP with hzero | hx
  · subst P
    simp
  · cases P with
    | zero =>
        simp [xCoordGood, ordPi_zero] at hx
    | some x y h =>
        simp only [xCoordGood] at hx
        have hx0 : x ≠ 0 := by
          intro hzero
          rw [hzero, ordPi_zero] at hx
          omega
        have hy0 : y ≠ 0 := yCoordGood_ne_zero_of_ordPi_x_neg h hx
        have hneg : WeierstrassCurve.Affine.Nonsingular E0Good x
            (WeierstrassCurve.Affine.negY E0Good x y) :=
          (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
        have hyneg0 : WeierstrassCurve.Affine.negY E0Good x y ≠ 0 :=
          yCoordGood_ne_zero_of_ordPi_x_neg hneg hx
        have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
        have heqneg := (WeierstrassCurve.Affine.equation_iff x
          (WeierstrassCurve.Affine.negY E0Good x y)).mp hneg.1
        have hcoords := MazurProof.N18RouteC.GoodModel.val_coords
          hx0 hy0 (by simpa using heq) hx
        have hcoordsNeg := MazurProof.N18RouteC.GoodModel.val_coords
          hx0 hyneg0 (by simpa using heqneg) hx
        have hz0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
        have hzneg0 :
            -x / WeierstrassCurve.Affine.negY E0Good x y ≠ 0 :=
          div_ne_zero (neg_ne_zero.mpr hx0) hyneg0
        rw [WeierstrassCurve.Affine.Point.neg_some,
          MazurProof.N18PackageII.zParamGood_some,
          MazurProof.N18PackageII.zParamGood_some,
          vpiGood_apply_of_ne hzneg0, vpiGood_apply_of_ne hz0]
        exact_mod_cast (show
          ordPi (-x / WeierstrassCurve.Affine.negY E0Good x y) =
            ordPi (-x / y) by omega)

/-! The following chart calculation is deliberately local to this file.  It
uses only integrality of the five coefficients of `E0Good`; in particular it
does not use the coefficient-specific identity from `N18AddCongrProof`. -/

private def OrdGoodG (N : ℤ) (x : L) : Prop := x = 0 ∨ N ≤ ordPi x

private theorem OrdGoodG.neg {N : ℤ} {x : L} (hx : OrdGoodG N x) :
    OrdGoodG N (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [ordPi_neg]

private theorem OrdGoodG.add {N : ℤ} {x y : L}
    (hx : OrdGoodG N x) (hy : OrdGoodG N y) : OrdGoodG N (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  rcases hx with hx | hx
  · subst x
    simpa using hy.resolve_left (by intro h; apply hxy; simp [h])
  rcases hy with hy | hy
  · subst y
    simpa using hx
  by_cases hx0 : x = 0
  · simp only [hx0, zero_add] at hxy ⊢
    exact hy
  by_cases hy0 : y = 0
  · simp only [hy0, add_zero] at hxy ⊢
    exact hx
  exact le_trans (le_min hx hy) (ordPi_add_ge hx0 hy0 hxy)

private theorem OrdGoodG.sub {N : ℤ} {x y : L}
    (hx : OrdGoodG N x) (hy : OrdGoodG N y) : OrdGoodG N (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

private theorem OrdGoodG.mul {M N : ℤ} {x y : L}
    (hx : OrdGoodG M x) (hy : OrdGoodG N y) : OrdGoodG (M + N) (x * y) := by
  rcases hx with rfl | hx
  · left; simp
  rcases hy with rfl | hy
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  by_cases hy0 : y = 0
  · left; simp [hy0]
  right
  rw [ordPi_mul hx0 hy0]
  omega

private theorem OrdGoodG.mono {M N : ℤ} {x : L}
    (hMN : M ≤ N) (hx : OrdGoodG N x) : OrdGoodG M x := by
  rcases hx with rfl | hx
  · left; rfl
  · right; omega

private theorem OrdGoodG.nat_mul (n : ℕ) {N : ℤ} {x : L}
    (hx : OrdGoodG N x) : OrdGoodG N ((n : L) * x) := by
  by_cases hn : (n : L) = 0
  · left; simp [hn]
  rcases hx with rfl | hx
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  right
  rw [ordPi_mul hn hx0]
  have hnval := zero_le_ordPi_intCast (n : ℤ)
  norm_num at hnval ⊢
  omega

private theorem OrdGoodG.div_unit {N : ℤ} {x y : L}
    (hx : OrdGoodG N x) (hy0 : y ≠ 0) (hyv : ordPi y = 0) :
    OrdGoodG N (x / y) := by
  rcases hx with rfl | hx
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  right
  rw [ordPi_div hx0 hy0, hyv]
  omega

private theorem OrdGoodG.unit_one_add {q : L} (hq : OrdGoodG 1 q) :
    1 + q ≠ 0 ∧ ordPi (1 + q) = 0 := by
  rcases hq with rfl | hq
  · simp [ordPi_one]
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hq
    omega
  constructor
  · intro h
    have : q = -1 := by linear_combination h
    rw [this, ordPi_neg, ordPi_one] at hq
    omega
  · simpa only [ordPi_one] using
      ordPi_add_eq_of_lt one_ne_zero hq0 (by rw [ordPi_one]; omega)

private theorem good_coeff_orders :
    0 ≤ ordPi E0Good.a₁ ∧ 0 ≤ ordPi E0Good.a₂ ∧
    0 ≤ ordPi E0Good.a₃ ∧ 0 ≤ ordPi E0Good.a₄ ∧
    0 ≤ ordPi E0Good.a₆ := by
  have hmap := MazurProof.N18PackageII.E0GoodInt_map
  have h1 := congrArg (fun W : WeierstrassCurve L ↦ W.a₁) hmap
  have h2 := congrArg (fun W : WeierstrassCurve L ↦ W.a₂) hmap
  have h3 := congrArg (fun W : WeierstrassCurve L ↦ W.a₃) hmap
  have h4 := congrArg (fun W : WeierstrassCurve L ↦ W.a₄) hmap
  have h6 := congrArg (fun W : WeierstrassCurve L ↦ W.a₆) hmap
  simp only [WeierstrassCurve.map_a₁] at h1
  simp only [WeierstrassCurve.map_a₂] at h2
  simp only [WeierstrassCurve.map_a₃] at h3
  simp only [WeierstrassCurve.map_a₄] at h4
  simp only [WeierstrassCurve.map_a₆] at h6
  rw [← h1, ← h2, ← h3, ← h4, ← h6]
  exact ⟨GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _⟩

private theorem ordPi_mul_nonneg_good {u w : L}
    (hu : 0 ≤ ordPi u) (hw : 0 ≤ ordPi w) :
    0 ≤ ordPi (u * w) := by
  by_cases hu0 : u = 0
  · simp [hu0, ordPi_zero]
  by_cases hw0 : w = 0
  · simp [hw0, ordPi_zero]
  rw [ordPi_mul hu0 hw0]
  omega

private theorem ordPi_le_mul_right_good {u w : L}
    (hu : 0 ≤ ordPi u) (hw : ordPi w ≤ 0) :
    ordPi w ≤ ordPi (u * w) := by
  by_cases hu0 : u = 0
  · simp [hu0, ordPi_zero, hw]
  by_cases hw0 : w = 0
  · simp [hw0, ordPi_zero]
  rw [ordPi_mul hu0 hw0]
  omega

/-- Integrality of `x` forces integrality of `y` on the good equation. -/
private theorem y_nonneg_of_x_nonneg_good {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) : 0 ≤ ordPi y := by
  by_cases hy0 : y = 0
  · simp [hy0, ordPi_zero]
  by_contra hy
  have hyneg : ordPi y < 0 := lt_of_not_ge hy
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have hx2 : 0 ≤ ordPi (x ^ 2) := by
    rw [pow_two]
    exact ordPi_mul_nonneg_good hx hx
  have hx3 : 0 ≤ ordPi (x ^ 3) := by
    rw [show x ^ 3 = x ^ 2 * x by ring]
    exact ordPi_mul_nonneg_good hx2 hx
  have hrhs : 0 ≤ ordPi
      (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    have h2 := ordPi_mul_nonneg_good ha2 hx2
    have h4 := ordPi_mul_nonneg_good ha4 hx
    exact le_ordPi_add
      (le_ordPi_add (le_ordPi_add hx3 h2 le_rfl) h4 le_rfl) ha6 le_rfl
  let tail := E0Good.a₁ * x * y + E0Good.a₃ * y
  have htail : ordPi y ≤ ordPi tail := by
    have hax : 0 ≤ ordPi (E0Good.a₁ * x) :=
      ordPi_mul_nonneg_good ha1 hx
    have h1 : ordPi y ≤ ordPi (E0Good.a₁ * x * y) :=
      ordPi_le_mul_right_good hax hyneg.le
    have h3 : ordPi y ≤ ordPi (E0Good.a₃ * y) :=
      ordPi_le_mul_right_good ha3 hyneg.le
    exact le_ordPi_add h1 h3 hyneg.le
  have hy2 : ordPi (y ^ 2) = 2 * ordPi y := by
    rw [pow_two, ordPi_mul hy0 hy0]
    ring
  have hlhs : ordPi (y ^ 2 + tail) = 2 * ordPi y := by
    by_cases ht0 : tail = 0
    · simp [ht0, hy2]
    · rw [ordPi_add_eq_of_lt (pow_ne_zero 2 hy0) ht0 (by
          rw [hy2]
          omega), hy2]
  have hcurve := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  have hcurve' : y ^ 2 + tail =
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ := by
    simpa only [tail, add_assoc] using hcurve
  have hrhs0 :
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ ≠ 0 := by
    intro hz
    have hlhs0 : y ^ 2 + tail = 0 := hcurve'.trans hz
    have hord := congrArg ordPi hlhs0
    rw [hlhs, ordPi_zero] at hord
    omega
  have hord := congrArg ordPi hcurve'
  rw [hlhs] at hord
  omega

private theorem good_a1_unit : E0Good.a₁ ≠ 0 ∧ ordPi E0Good.a₁ = 0 := by
  let c : MazurProof.N18PackageII.OL :=
    FieldArithmetic.aInteger ^ 2 - FieldArithmetic.aInteger - 1
  have hc : 0 ≤ ordPi ((c : MazurProof.N18PackageII.OL) : L) :=
    GoodModel.zero_le_ordPi_ringOfIntegers c
  have hmul : E0Good.a₁ * (c : L) = 1 := by
    change E0Good.a₁ * (a ^ 2 - a - 1) = 1
    simp only [E0Good]
    ring_nf
    simp only [a_pow_four, a_cubic]
    ring
  have ha0 : E0Good.a₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  have hc0 : (c : L) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact zero_ne_one hmul
  refine ⟨ha0, ?_⟩
  have hv := congrArg ordPi hmul
  rw [ordPi_mul ha0 hc0, ordPi_one] at hv
  have ha := good_coeff_orders.1
  omega

private def GGood (t w : L) : L :=
  w - E0Good.a₁ * t * w - E0Good.a₂ * t ^ 2 * w -
    E0Good.a₃ * w ^ 2 - E0Good.a₄ * t * w ^ 2 -
    E0Good.a₆ * w ^ 3 - t ^ 3

private def AGood (m : L) : L :=
  1 + E0Good.a₂ * m + E0Good.a₄ * m ^ 2 + E0Good.a₆ * m ^ 3

private def BGood (m b : L) : L :=
  E0Good.a₁ * m + E0Good.a₂ * b + E0Good.a₃ * m ^ 2 +
    2 * E0Good.a₄ * m * b + 3 * E0Good.a₆ * m ^ 2 * b

private def CGood (m b : L) : L :=
  m - E0Good.a₁ * b - 2 * E0Good.a₃ * m * b -
    E0Good.a₄ * b ^ 2 - 3 * E0Good.a₆ * m * b ^ 2

private def DGood (b : L) : L :=
  b - E0Good.a₃ * b ^ 2 - E0Good.a₆ * b ^ 3

private theorem GGood_line (t m b : L) :
    GGood t (m * t + b) =
      -AGood m * t ^ 3 - BGood m b * t ^ 2 +
        CGood m b * t + DGood b := by
  simp only [GGood, AGood, BGood, CGood, DGood]
  ring

private theorem chartGGood_eq_zero {x y : L} (hy0 : y ≠ 0)
    (heq : y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y =
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) :
    GGood (-x / y) (-1 / y) = 0 := by
  simp only [GGood] at heq ⊢
  field_simp [hy0]
  linear_combination -heq

private theorem secant_vieta_good (m b t₁ t₂ : L)
    (h₁ : GGood t₁ (m * t₁ + b) = 0)
    (h₂ : GGood t₂ (m * t₂ + b) = 0)
    (ht : t₁ ≠ t₂) (hA : AGood m ≠ 0) :
    let u := -BGood m b / AGood m - t₁ - t₂
    AGood m * (t₁ + t₂ + u) + BGood m b = 0 ∧
    AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0 ∧
    AGood m * t₁ * t₂ * u = DGood b := by
  let u := -BGood m b / AGood m - t₁ - t₂
  have hp₁ := h₁
  have hp₂ := h₂
  rw [GGood_line] at hp₁ hp₂
  have hsum : AGood m * (t₁ + t₂ + u) + BGood m b = 0 := by
    dsimp [u]
    field_simp [hA]
    ring
  have hdiff :
      -AGood m * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
          BGood m b * (t₁ + t₂) + CGood m b = 0 := by
    have hmul : (t₁ - t₂) *
        (-AGood m * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
          BGood m b * (t₁ + t₂) + CGood m b) = 0 := by
      linear_combination hp₁ - hp₂
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ht)
  have hpair :
      AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0 := by
    linear_combination hdiff + (t₁ + t₂) * hsum
  have hprod : AGood m * t₁ * t₂ * u = DGood b := by
    linear_combination -hp₁ - t₁ ^ 2 * hsum + t₁ * hpair
  exact ⟨hsum, hpair, hprod⟩

private theorem vieta_x_sum_good (m b t₁ t₂ u : L)
    (hA : AGood m ≠ 0) (hb : b ≠ 0)
    (hsum : AGood m * (t₁ + t₂ + u) + BGood m b = 0)
    (hpair : AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0)
    (hprod : AGood m * t₁ * t₂ * u = DGood b) :
    let q := (m * t₁ + b) * (m * t₂ + b) * (m * u + b)
    q ≠ 0 ∧
    t₁ / (m * t₁ + b) + t₂ / (m * t₂ + b) + u / (m * u + b) =
      (m / b) ^ 2 + E0Good.a₁ * (m / b) - E0Good.a₂ := by
  let q := (m * t₁ + b) * (m * t₂ + b) * (m * u + b)
  let n := t₁ * (m * t₂ + b) * (m * u + b) +
    t₂ * (m * t₁ + b) * (m * u + b) +
    u * (m * t₁ + b) * (m * t₂ + b)
  have hcoeffQ :
      m ^ 3 * DGood b - m ^ 2 * b * CGood m b -
        m * b ^ 2 * BGood m b + b ^ 3 * AGood m - b ^ 3 = 0 := by
    simp only [AGood, BGood, CGood, DGood]
    ring
  have hprod0 : AGood m * t₁ * t₂ * u - DGood b = 0 :=
    sub_eq_zero.mpr hprod
  have hQ : AGood m * q = b ^ 3 := by
    dsimp [q]
    linear_combination m ^ 3 * hprod0 + m ^ 2 * b * hpair +
      m * b ^ 2 * hsum + hcoeffQ
  have hcoeffN :
      3 * m ^ 2 * DGood b - 2 * m * b * CGood m b -
        b ^ 2 * BGood m b -
        b * (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) = 0 := by
    simp only [BGood, CGood, DGood]
    ring
  have hN : AGood m * n =
      b * (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) := by
    dsimp [n]
    linear_combination 3 * m ^ 2 * hprod0 + 2 * m * b * hpair +
      b ^ 2 * hsum + hcoeffN
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ
    exact (pow_ne_zero 3 hb) hQ.symm
  have h₁0 : m * t₁ + b ≠ 0 := by
    intro h; apply hq0; simp [q, h]
  have h₂0 : m * t₂ + b ≠ 0 := by
    intro h; apply hq0; simp [q, h]
  have hu0 : m * u + b ≠ 0 := by
    intro h; apply hq0; simp [q, h]
  have h₁0' : t₁ * m + b ≠ 0 := by simpa only [mul_comm] using h₁0
  have h₂0' : t₂ * m + b ≠ 0 := by simpa only [mul_comm] using h₂0
  have hu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hu0
  have hcleared :
      b ^ 2 * n =
        (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) * q := by
    apply mul_left_cancel₀ hA
    linear_combination b ^ 2 * hN -
      (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) * hQ
  refine ⟨hq0, ?_⟩
  have hleft :
      t₁ / (m * t₁ + b) + t₂ / (m * t₂ + b) + u / (m * u + b) = n / q := by
    field_simp [hq0, h₁0, h₂0, hu0, h₁0', h₂0', hu0']
    simp only [n, q]
    ring
  rw [hleft]
  field_simp [hq0, hb]
  linear_combination hcleared

private theorem add_congr_inverse_good {x y : L}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hxneg : ordPi x < 0) :
    let P : GoodPoint := .some x y hns
    let r := ordPi (-x / y)
    InFormalKernel (P + (-P)) ∧
      (MazurProof.N18PackageII.zParamGood (P + (-P)) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood (-P) = 0 ∨
        2 * r ≤ ordPi
          (MazurProof.N18PackageII.zParamGood (P + (-P)) -
            MazurProof.N18PackageII.zParamGood P -
            MazurProof.N18PackageII.zParamGood (-P))) := by
  let P : GoodPoint := .some x y hns
  let r : ℤ := ordPi (-x / y)
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hns.1
  have hcoords := GoodModel.val_coords hx0 hy0 (by simpa using heq) hxneg
  have hxv : ordPi x = -2 * r := hcoords.1
  have hyv : ordPi y = -3 * r := hcoords.2
  have hr : 1 ≤ r := by omega
  have ha1 := good_a1_unit
  have ha3v := good_coeff_orders.2.2.1
  let s : L := E0Good.a₁ * x + E0Good.a₃
  have hax0 : E0Good.a₁ * x ≠ 0 := mul_ne_zero ha1.1 hx0
  have haxv : ordPi (E0Good.a₁ * x) = -2 * r := by
    rw [ordPi_mul ha1.1 hx0, ha1.2, hxv]
    omega
  have hs0 : s ≠ 0 := by
    intro hs
    have hneg : E0Good.a₃ = -(E0Good.a₁ * x) := by
      dsimp [s] at hs
      linear_combination hs
    have hv := congrArg ordPi hneg
    rw [ordPi_neg, haxv] at hv
    omega
  have hsv : ordPi s = -2 * r := by
    dsimp [s]
    by_cases ha30 : E0Good.a₃ = 0
    · rw [ha30, add_zero, haxv]
    · exact (ordPi_add_eq_of_lt hax0 ha30 (by rw [haxv]; omega)).trans haxv
  let d : L := y + s
  have hd0 : d ≠ 0 := by
    intro hd
    have hsEq : s = -y := by
      dsimp [d] at hd
      linear_combination hd
    have hv := congrArg ordPi hsEq
    rw [ordPi_neg, hsv, hyv] at hv
    omega
  have hdv : ordPi d = -3 * r := by
    dsimp [d]
    exact (ordPi_add_eq_of_lt hy0 hs0 (by rw [hyv, hsv]; omega)).trans hyv
  have hzneg : MazurProof.N18PackageII.zParamGood (-P) = x / d := by
    change -x / WeierstrassCurve.Affine.negY E0Good x y = x / d
    rw [show WeierstrassCurve.Affine.negY E0Good x y = -d by
      simp only [WeierstrassCurve.Affine.negY]
      dsimp [d, s]
      ring]
    field_simp [hd0]
  have herr :
      (0 : L) - (-x / y) - x / d = x * s / (y * d) := by
    calc
      (0 : L) - (-x / y) - x / d = x / y - x / d := by ring
      _ = (x * d - y * x) / (y * d) := div_sub_div x x hy0 hd0
      _ = x * s / (y * d) := by
        congr 1
        dsimp only [d]
        ring
  have herr0 : x * s / (y * d) ≠ 0 :=
    div_ne_zero (mul_ne_zero hx0 hs0) (mul_ne_zero hy0 hd0)
  have herrv : ordPi (x * s / (y * d)) = 2 * r := by
    rw [ordPi_div (mul_ne_zero hx0 hs0) (mul_ne_zero hy0 hd0),
      ordPi_mul hx0 hs0, ordPi_mul hy0 hd0, hxv, hsv, hyv, hdv]
    omega
  dsimp only
  refine ⟨Or.inl (add_neg_cancel P), ?_⟩
  right
  rw [show P + -P = 0 by exact add_neg_cancel P,
    MazurProof.N18PackageII.zParamGood_zero, hzneg]
  change 2 * ordPi (-x / y) ≤ ordPi ((0 : L) - (-x / y) - x / d)
  rw [herr, herrv]

private theorem line_valuation_good (r : ℤ) (t₁ t₂ m b : L)
    (hr : 1 ≤ r) (ht₁ : OrdGoodG r t₁) (ht₂ : OrdGoodG r t₂)
    (hm : OrdGoodG (2 * r) m) (hb : OrdGoodG (3 * r) b) :
    let u := -BGood m b / AGood m - t₁ - t₂
    let d := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
    let t₃ := -u / d
    (AGood m ≠ 0 ∧ ordPi (AGood m) = 0) ∧
    (d ≠ 0 ∧ ordPi d = 0) ∧ OrdGoodG r u ∧
    (t₃ - t₁ - t₂ = 0 ∨ 2 * r ≤ ordPi (t₃ - t₁ - t₂)) := by
  let u := -BGood m b / AGood m - t₁ - t₂
  let d := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
  let t₃ := -u / d
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have c1 : OrdGoodG 0 E0Good.a₁ := Or.inr ha1
  have c2 : OrdGoodG 0 E0Good.a₂ := Or.inr ha2
  have c3 : OrdGoodG 0 E0Good.a₃ := Or.inr ha3
  have c4 : OrdGoodG 0 E0Good.a₄ := Or.inr ha4
  have c6 : OrdGoodG 0 E0Good.a₆ := Or.inr ha6
  have hm1 : OrdGoodG 1 m := hm.mono (by omega)
  have hmSq1 : OrdGoodG 1 (m ^ 2) := by
    rw [pow_two]
    exact (hm1.mul hm1).mono (by omega)
  have hmCube1 : OrdGoodG 1 (m ^ 3) := by
    rw [show m ^ 3 = m ^ 2 * m by ring]
    exact (hmSq1.mul hm1).mono (by omega)
  let qA := E0Good.a₂ * m + E0Good.a₄ * m ^ 2 + E0Good.a₆ * m ^ 3
  have hqA : OrdGoodG 1 qA := by
    dsimp [qA]
    exact ((c2.mul hm1).mono (by omega) |>.add
      ((c4.mul hmSq1).mono (by omega))).add
      ((c6.mul hmCube1).mono (by omega))
  have hAeq : AGood m = 1 + qA := by simp only [AGood, qA]; ring
  have hAunit : AGood m ≠ 0 ∧ ordPi (AGood m) = 0 := by
    rw [hAeq]
    exact hqA.unit_one_add
  have hmSq : OrdGoodG (2 * r) (m ^ 2) := by
    rw [pow_two]
    exact (hm.mul hm).mono (by omega)
  have hb2 : OrdGoodG (2 * r) b := hb.mono (by omega)
  have hmb : OrdGoodG (2 * r) (m * b) := (hm.mul hb).mono (by omega)
  have hmSqb : OrdGoodG (2 * r) (m ^ 2 * b) :=
    (hmSq.mul hb).mono (by omega)
  have hB : OrdGoodG (2 * r) (BGood m b) := by
    simp only [BGood]
    have h1 : OrdGoodG (2 * r) (E0Good.a₁ * m) :=
      (c1.mul hm).mono (by omega)
    have h2 : OrdGoodG (2 * r) (E0Good.a₂ * b) :=
      (c2.mul hb2).mono (by omega)
    have h3 : OrdGoodG (2 * r) (E0Good.a₃ * m ^ 2) :=
      (c3.mul hmSq).mono (by omega)
    have h4base : OrdGoodG (2 * r) (E0Good.a₄ * (m * b)) := by
      simpa only [zero_add] using c4.mul hmb
    have h4 : OrdGoodG (2 * r) (2 * E0Good.a₄ * m * b) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using h4base.nat_mul 2
    have h6base : OrdGoodG (2 * r) (E0Good.a₆ * (m ^ 2 * b)) := by
      simpa only [zero_add] using c6.mul hmSqb
    have h6 : OrdGoodG (2 * r) (3 * E0Good.a₆ * m ^ 2 * b) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using h6base.nat_mul 3
    exact (((h1.add h2).add h3).add h4).add h6
  have hu : OrdGoodG r u := by
    dsimp [u]
    have hquot : OrdGoodG (2 * r) (-BGood m b / AGood m) :=
      hB.neg.div_unit hAunit.1 hAunit.2
    exact ((hquot.mono (by omega)).sub ht₁).sub ht₂
  have hsumA1 : OrdGoodG 0 (E0Good.a₁ + E0Good.a₃ * m) := by
    exact c1.add ((c3.mul hm).mono (by omega))
  have hk : OrdGoodG r
      ((E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b) := by
    exact (hsumA1.mul hu |>.mono (by omega)).add
      ((c3.mul hb).mono (by omega))
  have hqD : OrdGoodG 1
      (-((E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b)) :=
    hk.neg.mono (by omega)
  have hdEq : d = 1 +
      (-((E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b)) := by
    dsimp [d]
    ring
  have hdunit : d ≠ 0 ∧ ordPi d = 0 := by
    rw [hdEq]
    exact hqD.unit_one_add
  let k := (E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b
  have hk' : OrdGoodG r k := by simpa only [k] using hk
  have hfirst : OrdGoodG (2 * r) (BGood m b / AGood m) :=
    hB.div_unit hAunit.1 hAunit.2
  have hsecond : OrdGoodG (2 * r) (u * k / d) :=
    (hu.mul hk' |>.mono (by omega)).div_unit hdunit.1 hdunit.2
  let err := t₃ - t₁ - t₂
  have herrEq : err = BGood m b / AGood m - u * k / d := by
    have huEq : t₁ + t₂ = -BGood m b / AGood m - u := by
      dsimp only [u]
      ring
    have hdEq' : d = 1 - k := by
      dsimp only [d, k]
      ring
    have hdk : 1 - k ≠ 0 := by
      rw [← hdEq']
      exact hdunit.1
    calc
      err = -u / d - (t₁ + t₂) := by dsimp only [err, t₃]; ring
      _ = -u / d - (-BGood m b / AGood m - u) := by rw [huEq]
      _ = BGood m b / AGood m - u * k / d := by
        rw [hdEq']
        field_simp [hAunit.1, hdk]
        ring
  have herrGood : OrdGoodG (2 * r) err := by
    rw [herrEq]
    exact hfirst.sub hsecond
  refine ⟨hAunit, hdunit, hu, ?_⟩
  exact herrGood

private theorem add_congr_distinct_good {x₁ y₁ x₂ y₂ : L}
    (hx₁0 : x₁ ≠ 0) (hy₁0 : y₁ ≠ 0)
    (hx₂0 : x₂ ≠ 0) (hy₂0 : y₂ ≠ 0)
    (hns₁ : WeierstrassCurve.Affine.Nonsingular E0Good x₁ y₁)
    (hns₂ : WeierstrassCurve.Affine.Nonsingular E0Good x₂ y₂)
    (hxne : x₁ ≠ x₂) (hx₁neg : ordPi x₁ < 0) (hx₂neg : ordPi x₂ < 0) :
    let P : GoodPoint := .some x₁ y₁ hns₁
    let Q : GoodPoint := .some x₂ y₂ hns₂
    let r := min (ordPi (-x₁ / y₁)) (ordPi (-x₂ / y₂))
    InFormalKernel (P + Q) ∧
      (MazurProof.N18PackageII.zParamGood (P + Q) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood Q = 0 ∨
        2 * r ≤ ordPi
          (MazurProof.N18PackageII.zParamGood (P + Q) -
            MazurProof.N18PackageII.zParamGood P -
            MazurProof.N18PackageII.zParamGood Q)) := by
  let P : GoodPoint := .some x₁ y₁ hns₁
  let Q : GoodPoint := .some x₂ y₂ hns₂
  let t₁ : L := -x₁ / y₁
  let w₁ : L := -1 / y₁
  let t₂ : L := -x₂ / y₂
  let w₂ : L := -1 / y₂
  let r₁ : ℤ := ordPi t₁
  let r₂ : ℤ := ordPi t₂
  let r : ℤ := min r₁ r₂
  have heq₁ := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hns₁.1
  have heq₂ := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp hns₂.1
  have hc₁ := GoodModel.val_coords hx₁0 hy₁0 (by simpa using heq₁) hx₁neg
  have hc₂ := GoodModel.val_coords hx₂0 hy₂0 (by simpa using heq₂) hx₂neg
  have hx₁v : ordPi x₁ = -2 * r₁ := hc₁.1
  have hy₁v : ordPi y₁ = -3 * r₁ := hc₁.2
  have hx₂v : ordPi x₂ = -2 * r₂ := hc₂.1
  have hy₂v : ordPi y₂ = -3 * r₂ := hc₂.2
  have hr₁ : 1 ≤ r₁ := by omega
  have hr₂ : 1 ≤ r₂ := by omega
  have hr : 1 ≤ r := by simp only [r, le_min_iff]; exact ⟨hr₁, hr₂⟩
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := min_le_right _ _
  have ht₁0 : t₁ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₁0) hy₁0
  have ht₂0 : t₂ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₂0) hy₂0
  have hw₁0 : w₁ ≠ 0 := div_ne_zero (by norm_num) hy₁0
  have hw₂0 : w₂ ≠ 0 := div_ne_zero (by norm_num) hy₂0
  have hw₁v : ordPi w₁ = 3 * r₁ := by
    dsimp [w₁]
    rw [ordPi_div (by norm_num) hy₁0, ordPi_neg, ordPi_one, hy₁v]
    omega
  have hw₂v : ordPi w₂ = 3 * r₂ := by
    dsimp [w₂]
    rw [ordPi_div (by norm_num) hy₂0, ordPi_neg, ordPi_one, hy₂v]
    omega
  have ht₁r : OrdGoodG r t₁ := Or.inr hrr₁
  have ht₂r : OrdGoodG r t₂ := Or.inr hrr₂
  have hw₁r : OrdGoodG (3 * r) w₁ := Or.inr (by rw [hw₁v]; omega)
  have hw₂r : OrdGoodG (3 * r) w₂ := Or.inr (by rw [hw₂v]; omega)
  have hG₁ : GGood t₁ w₁ = 0 := chartGGood_eq_zero hy₁0 heq₁
  have hG₂ : GGood t₂ w₂ = 0 := chartGGood_eq_zero hy₂0 heq₂
  let SU : L := 1 - E0Good.a₁ * t₂ - E0Good.a₂ * t₂ ^ 2 -
    E0Good.a₃ * (w₁ + w₂) - E0Good.a₄ * t₂ * (w₁ + w₂) -
    E0Good.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  let SN : L := E0Good.a₁ * w₁ + E0Good.a₂ * (t₁ + t₂) * w₁ +
    E0Good.a₄ * w₁ ^ 2 + (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)
  have hcross : (w₁ - w₂) * SU = (t₁ - t₂) * SN := by
    dsimp [SU, SN]
    simp only [GGood] at hG₁ hG₂
    linear_combination hG₁ - hG₂
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have c1 : OrdGoodG 0 E0Good.a₁ := Or.inr ha1
  have c2 : OrdGoodG 0 E0Good.a₂ := Or.inr ha2
  have c3 : OrdGoodG 0 E0Good.a₃ := Or.inr ha3
  have c4 : OrdGoodG 0 E0Good.a₄ := Or.inr ha4
  have c6 : OrdGoodG 0 E0Good.a₆ := Or.inr ha6
  have ht₂1 : OrdGoodG 1 t₂ := ht₂r.mono (by omega)
  have hw₁1 : OrdGoodG 1 w₁ := hw₁r.mono (by omega)
  have hw₂1 : OrdGoodG 1 w₂ := hw₂r.mono (by omega)
  have hwsum1 : OrdGoodG 1 (w₁ + w₂) := hw₁1.add hw₂1
  have ht₂sq1 : OrdGoodG 1 (t₂ ^ 2) := by
    rw [pow_two]
    exact (ht₂1.mul ht₂1).mono (by omega)
  have hww1 : OrdGoodG 1 (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) := by
    have h11 : OrdGoodG 1 (w₁ ^ 2) := by
      rw [pow_two]; exact (hw₁1.mul hw₁1).mono (by omega)
    have h12 : OrdGoodG 1 (w₁ * w₂) := (hw₁1.mul hw₂1).mono (by omega)
    have h22 : OrdGoodG 1 (w₂ ^ 2) := by
      rw [pow_two]; exact (hw₂1.mul hw₂1).mono (by omega)
    exact (h11.add h12).add h22
  let qSU : L := -E0Good.a₁ * t₂ - E0Good.a₂ * t₂ ^ 2 -
    E0Good.a₃ * (w₁ + w₂) - E0Good.a₄ * t₂ * (w₁ + w₂) -
    E0Good.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  have hqSU : OrdGoodG 1 qSU := by
    dsimp [qSU]
    have h1 : OrdGoodG 1 (-E0Good.a₁ * t₂) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₁ * t₂)) from
          (by simpa only [zero_add] using c1.mul ht₂1 :
            OrdGoodG 1 (E0Good.a₁ * t₂)).neg)
    have h2 : OrdGoodG 1 (-E0Good.a₂ * t₂ ^ 2) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₂ * t₂ ^ 2)) from
          (by simpa only [zero_add] using c2.mul ht₂sq1 :
            OrdGoodG 1 (E0Good.a₂ * t₂ ^ 2)).neg)
    have h3 : OrdGoodG 1 (-E0Good.a₃ * (w₁ + w₂)) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₃ * (w₁ + w₂))) from
          (by simpa only [zero_add] using c3.mul hwsum1 :
            OrdGoodG 1 (E0Good.a₃ * (w₁ + w₂))).neg)
    have h4base : OrdGoodG (1 + 1) (E0Good.a₄ * (t₂ * (w₁ + w₂))) := by
      simpa only [zero_add] using c4.mul (ht₂1.mul hwsum1)
    have h4 : OrdGoodG 1 (-E0Good.a₄ * t₂ * (w₁ + w₂)) := by
      simpa only [neg_mul, mul_assoc] using (h4base.mono (by norm_num)).neg
    have h6 : OrdGoodG 1
        (-E0Good.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) := by
      simpa only [neg_mul, zero_add] using (c6.mul hww1).neg
    simpa only [sub_eq_add_neg, neg_mul] using (((h1.add h2).add h3).add h4).add h6
  have hSUeq : SU = 1 + qSU := by simp only [SU, qSU]; ring
  have hSUunit : SU ≠ 0 ∧ ordPi SU = 0 := by
    rw [hSUeq]
    exact hqSU.unit_one_add
  have htne : t₁ ≠ t₂ := by
    intro ht
    have hwdiff : w₁ - w₂ = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hSUunit.1
      rw [hcross, ht, sub_self, zero_mul]
    have hw : w₁ = w₂ := sub_eq_zero.mp hwdiff
    apply hxne
    have hx₁tw : x₁ = t₁ / w₁ := by
      dsimp [t₁, w₁]; field_simp [hy₁0]
    have hx₂tw : x₂ = t₂ / w₂ := by
      dsimp [t₂, w₂]; field_simp [hy₂0]
    rw [hx₁tw, hx₂tw, ht, hw]
  let m : L := (w₁ - w₂) / (t₁ - t₂)
  let b : L := w₁ - m * t₁
  have hline₁ : w₁ = m * t₁ + b := by dsimp [b]; ring
  have hline₂ : w₂ = m * t₂ + b := by
    dsimp [m, b]
    field_simp [sub_ne_zero.mpr htne]
    ring
  have hmEq : SU * m = SN := by
    dsimp [m]
    field_simp [sub_ne_zero.mpr htne]
    linear_combination hcross
  have hsumr : OrdGoodG r (t₁ + t₂) := ht₁r.add ht₂r
  have hSN : OrdGoodG (2 * r) SN := by
    have h1 : OrdGoodG (2 * r) (E0Good.a₁ * w₁) :=
      (c1.mul hw₁r).mono (by omega)
    have h2 : OrdGoodG (2 * r) (E0Good.a₂ * (t₁ + t₂) * w₁) :=
      (c2.mul hsumr |>.mul hw₁r).mono (by omega)
    have h4 : OrdGoodG (2 * r) (E0Good.a₄ * w₁ ^ 2) := by
      rw [pow_two]
      exact (c4.mul (hw₁r.mul hw₁r)).mono (by omega)
    have htt : OrdGoodG (2 * r) (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) := by
      have h11 : OrdGoodG (2 * r) (t₁ ^ 2) := by
        rw [pow_two]; simpa only [two_mul] using ht₁r.mul ht₁r
      have h12 : OrdGoodG (2 * r) (t₁ * t₂) := by
        simpa only [two_mul] using ht₁r.mul ht₂r
      have h22 : OrdGoodG (2 * r) (t₂ ^ 2) := by
        rw [pow_two]; simpa only [two_mul] using ht₂r.mul ht₂r
      exact (h11.add h12).add h22
    dsimp [SN]
    exact ((h1.add h2).add h4).add htt
  have hmGood : OrdGoodG (2 * r) m := by
    rcases hSN with hSN | hSN
    · left
      apply (mul_eq_zero.mp ?_).resolve_left hSUunit.1
      rw [hmEq, hSN]
    · have hSN0 : SN ≠ 0 := by
        intro h; rw [h, ordPi_zero] at hSN; omega
      have hm0 : m ≠ 0 := by
        intro h; rw [h, mul_zero] at hmEq; exact hSN0 hmEq.symm
      right
      have hv := congrArg ordPi hmEq
      rw [ordPi_mul hSUunit.1 hm0, hSUunit.2] at hv
      omega
  have hbGood : OrdGoodG (3 * r) b := by
    have hmt : OrdGoodG (3 * r) (m * t₁) :=
      (hmGood.mul ht₁r).mono (by omega)
    dsimp [b]
    exact hw₁r.sub hmt
  have hb0 : b ≠ 0 := by
    intro hb
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hb, hm0, zero_mul, add_zero] at hline₁
      exact hw₁0 hline₁
    apply hxne
    have hx₁tw : x₁ = t₁ / w₁ := by
      dsimp [t₁, w₁]; field_simp [hy₁0]
    have hx₂tw : x₂ = t₂ / w₂ := by
      dsimp [t₂, w₂]; field_simp [hy₂0]
    rw [hx₁tw, hx₂tw, hline₁, hline₂, hb]
    field_simp [hm0, ht₁0, ht₂0]
    ring
  let u : L := -BGood m b / AGood m - t₁ - t₂
  let d : L := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
  let t₃ : L := -u / d
  have hval := line_valuation_good r t₁ t₂ m b hr ht₁r ht₂r hmGood hbGood
  change (AGood m ≠ 0 ∧ ordPi (AGood m) = 0) ∧
    (d ≠ 0 ∧ ordPi d = 0) ∧ OrdGoodG r u ∧
    (t₃ - t₁ - t₂ = 0 ∨ 2 * r ≤ ordPi (t₃ - t₁ - t₂)) at hval
  rcases hval with ⟨hAunit, hdunit, huGood, herr⟩
  have hlineG₁ : GGood t₁ (m * t₁ + b) = 0 := by
    rw [← hline₁]; exact hG₁
  have hlineG₂ : GGood t₂ (m * t₂ + b) = 0 := by
    rw [← hline₂]; exact hG₂
  have hvieta := secant_vieta_good m b t₁ t₂ hlineG₁ hlineG₂ htne hAunit.1
  change AGood m * (t₁ + t₂ + u) + BGood m b = 0 ∧
    AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0 ∧
    AGood m * t₁ * t₂ * u = DGood b at hvieta
  rcases hvieta with ⟨hsum, hpair, hprod⟩
  have hxsumData := vieta_x_sum_good m b t₁ t₂ u hAunit.1 hb0 hsum hpair hprod
  dsimp only at hxsumData
  rcases hxsumData with ⟨hqprod, hxsum⟩
  have hmu0 : m * u + b ≠ 0 := by
    intro h; apply hqprod; simp [h]
  have hmt₁0 : m * t₁ + b ≠ 0 := by simpa only [← hline₁] using hw₁0
  have hmt₂0 : m * t₂ + b ≠ 0 := by simpa only [← hline₂] using hw₂0
  have hx₁chart : x₁ = t₁ / (m * t₁ + b) := by
    rw [← hline₁]; dsimp [t₁, w₁]; field_simp [hy₁0]
  have hx₂chart : x₂ = t₂ / (m * t₂ + b) := by
    rw [← hline₂]; dsimp [t₂, w₂]; field_simp [hy₂0]
  have hy₁chart : y₁ = -1 / (m * t₁ + b) := by
    rw [← hline₁]; dsimp [w₁]; field_simp [hy₁0]
  have hy₂chart : y₂ = -1 / (m * t₂ + b) := by
    rw [← hline₂]; dsimp [w₂]; field_simp [hy₂0]
  let ell := WeierstrassCurve.Affine.slope E0Good x₁ x₂ y₁ y₂
  have hell : ell = m / b := by
    dsimp only [ell]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
    rw [hx₁chart, hx₂chart, hy₁chart, hy₂chart]
    have hxdiff :
        t₁ / (m * t₁ + b) - t₂ / (m * t₂ + b) ≠ 0 := by
      simpa only [← hx₁chart, ← hx₂chart] using sub_ne_zero.mpr hxne
    have hbdiff : -(b * t₂) + b * t₁ ≠ 0 := by
      rw [show -(b * t₂) + b * t₁ = b * (t₁ - t₂) by ring]
      exact mul_ne_zero hb0 (sub_ne_zero.mpr htne)
    field_simp [hmt₁0, hmt₂0, hxdiff, hb0, hbdiff]
    calc
      b * (-(m * t₂ + b) - -(m * t₁ + b)) /
          (t₁ * (m * t₂ + b) - (m * t₁ + b) * t₂) =
          m * (-(b * t₂) + b * t₁) / (-(b * t₂) + b * t₁) := by
            congr 1 <;> ring
      _ = m := by
        have htdiff : -t₂ + t₁ ≠ 0 := by
          simpa only [neg_add_eq_sub, sub_ne_zero] using htne
        field_simp [htdiff]
  let x₃ := WeierstrassCurve.Affine.addX E0Good x₁ x₂ ell
  have hx₃ : x₃ = u / (m * u + b) := by
    change ell ^ 2 + E0Good.a₁ * ell - E0Good.a₂ - x₁ - x₂ =
      u / (m * u + b)
    rw [hell, hx₁chart, hx₂chart, ← hxsum]
    abel
  let ybar := WeierstrassCurve.Affine.negAddY E0Good x₁ x₂ y₁ ell
  have hybar : ybar = -1 / (m * u + b) := by
    change ell * (x₃ - x₁) + y₁ = -1 / (m * u + b)
    rw [hx₃, hell, hx₁chart, hy₁chart]
    field_simp [hb0, hmt₁0, hmu0]
    ring
  let y₃ := WeierstrassCurve.Affine.addY E0Good x₁ x₂ y₁ ell
  have hy₃ : y₃ = d / (m * u + b) := by
    change WeierstrassCurve.Affine.negY E0Good x₃ ybar = d / (m * u + b)
    rw [hybar, hx₃]
    simp only [WeierstrassCurve.Affine.negY]
    dsimp [d]
    field_simp [hmu0]
    ring
  have hbridge : MazurProof.N18PackageII.zParamGood (P + Q) = t₃ := by
    dsimp [P, Q]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    change -x₃ / y₃ = t₃
    rw [hx₃, hy₃]
    dsimp [t₃]
    have hmu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hmu0
    field_simp [hmu0, hmu0', hdunit.1]
  have hmuGood : OrdGoodG (3 * r) (m * u) :=
    (hmGood.mul huGood).mono (by omega)
  have hmubGood : OrdGoodG (3 * r) (m * u + b) :=
    hmuGood.add hbGood
  have hmubOrd : 3 * r ≤ ordPi (m * u + b) := by
    rcases hmubGood with hmubZero | hmubOrd
    · exact (hmu0 hmubZero).elim
    · exact hmubOrd
  have hns₃ : WeierstrassCurve.Affine.Nonsingular E0Good x₃ y₃ := by
    exact WeierstrassCurve.Affine.nonsingular_add hns₁ hns₂
      (fun hxy ↦ hxne hxy.1)
  have hy₃v : ordPi y₃ = -ordPi (m * u + b) := by
    rw [hy₃, ordPi_div hdunit.1 hmu0, hdunit.2]
    ring
  have hy₃neg : ordPi y₃ < 0 := by
    rw [hy₃v]
    omega
  have hx₃neg : ordPi x₃ < 0 := by
    by_contra hx₃
    have hy₃nonneg := y_nonneg_of_x_nonneg_good hns₃ (le_of_not_gt hx₃)
    omega
  have hformal : InFormalKernel (P + Q) := by
    dsimp only [P, Q]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    exact Or.inr hx₃neg
  dsimp only
  refine ⟨hformal, ?_⟩
  rw [hbridge]
  exact herr

private theorem add_congr_tangent_good {x y : L}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hxneg : ordPi x < 0)
    (hyne : WeierstrassCurve.Affine.negY E0Good x y ≠ y) :
    let P : GoodPoint := .some x y hns
    let r := ordPi (-x / y)
    InFormalKernel (P + P) ∧
      (MazurProof.N18PackageII.zParamGood (P + P) -
          2 * MazurProof.N18PackageII.zParamGood P = 0 ∨
        2 * r ≤ ordPi
          (MazurProof.N18PackageII.zParamGood (P + P) -
            2 * MazurProof.N18PackageII.zParamGood P)) := by
  let P : GoodPoint := .some x y hns
  let t : L := -x / y
  let w : L := -1 / y
  let r : ℤ := ordPi t
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hns.1
  have hc := GoodModel.val_coords hx0 hy0 (by simpa using heq) hxneg
  have hxv : ordPi x = -2 * r := hc.1
  have hyv : ordPi y = -3 * r := hc.2
  have hr : 1 ≤ r := by omega
  have ht0 : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
  have hw0 : w ≠ 0 := div_ne_zero (by norm_num) hy0
  have hwv : ordPi w = 3 * r := by
    dsimp [w]
    rw [ordPi_div (by norm_num) hy0, ordPi_neg, ordPi_one, hyv]
    omega
  have htGood : OrdGoodG r t := Or.inr (by rfl)
  have hwGood : OrdGoodG (3 * r) w := Or.inr (by rw [hwv])
  have hG : GGood t w = 0 := chartGGood_eq_zero hy0 heq
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have c1 : OrdGoodG 0 E0Good.a₁ := Or.inr ha1
  have c2 : OrdGoodG 0 E0Good.a₂ := Or.inr ha2
  have c3 : OrdGoodG 0 E0Good.a₃ := Or.inr ha3
  have c4 : OrdGoodG 0 E0Good.a₄ := Or.inr ha4
  have c6 : OrdGoodG 0 E0Good.a₆ := Or.inr ha6
  let TU : L := 1 - E0Good.a₁ * t - E0Good.a₂ * t ^ 2 -
    2 * E0Good.a₃ * w - 2 * E0Good.a₄ * t * w -
    3 * E0Good.a₆ * w ^ 2
  let TN : L := 3 * t ^ 2 + E0Good.a₁ * w +
    2 * E0Good.a₂ * t * w + E0Good.a₄ * w ^ 2
  have ht1 : OrdGoodG 1 t := htGood.mono (by omega)
  have hw1 : OrdGoodG 1 w := hwGood.mono (by omega)
  have htSq1 : OrdGoodG 1 (t ^ 2) := by
    rw [pow_two]; exact (ht1.mul ht1).mono (by omega)
  have hwSq1 : OrdGoodG 1 (w ^ 2) := by
    rw [pow_two]; exact (hw1.mul hw1).mono (by omega)
  let qTU : L := -E0Good.a₁ * t - E0Good.a₂ * t ^ 2 -
    2 * E0Good.a₃ * w - 2 * E0Good.a₄ * t * w -
    3 * E0Good.a₆ * w ^ 2
  have hqTU : OrdGoodG 1 qTU := by
    dsimp [qTU]
    have h1 : OrdGoodG 1 (-E0Good.a₁ * t) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₁ * t)) from
          (by simpa only [zero_add] using c1.mul ht1 :
            OrdGoodG 1 (E0Good.a₁ * t)).neg)
    have h2 : OrdGoodG 1 (-E0Good.a₂ * t ^ 2) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₂ * t ^ 2)) from
          (by simpa only [zero_add] using c2.mul htSq1 :
            OrdGoodG 1 (E0Good.a₂ * t ^ 2)).neg)
    have h3base : OrdGoodG 1 (E0Good.a₃ * w) := by
      simpa only [zero_add] using c3.mul hw1
    have h3 : OrdGoodG 1 (-2 * E0Good.a₃ * w) := by
      simpa only [Nat.cast_ofNat, neg_mul, mul_assoc] using
        (h3base.nat_mul 2).neg
    have h4base : OrdGoodG (1 + 1) (E0Good.a₄ * (t * w)) := by
      simpa only [zero_add] using c4.mul (ht1.mul hw1)
    have h4 : OrdGoodG 1 (-2 * E0Good.a₄ * t * w) := by
      simpa only [Nat.cast_ofNat, neg_mul, mul_assoc] using
        ((h4base.mono (by norm_num)).nat_mul 2).neg
    have h6base : OrdGoodG 1 (E0Good.a₆ * w ^ 2) := by
      simpa only [zero_add] using c6.mul hwSq1
    have h6 : OrdGoodG 1 (-3 * E0Good.a₆ * w ^ 2) := by
      simpa only [Nat.cast_ofNat, neg_mul, mul_assoc] using
        (h6base.nat_mul 3).neg
    simpa only [sub_eq_add_neg, neg_mul] using (((h1.add h2).add h3).add h4).add h6
  have hTUeq : TU = 1 + qTU := by simp only [TU, qTU]; ring
  have hTUunit : TU ≠ 0 ∧ ordPi TU = 0 := by
    rw [hTUeq]
    exact hqTU.unit_one_add
  have htSq : OrdGoodG (2 * r) (t ^ 2) := by
    rw [pow_two]; simpa only [two_mul] using htGood.mul htGood
  have hw2 : OrdGoodG (2 * r) w := hwGood.mono (by omega)
  have hTN : OrdGoodG (2 * r) TN := by
    have h0 := htSq.nat_mul 3
    have h1 : OrdGoodG (2 * r) (E0Good.a₁ * w) :=
      (c1.mul hw2).mono (by omega)
    have h2base : OrdGoodG (2 * r) (E0Good.a₂ * (t * w)) :=
      (c2.mul (htGood.mul hwGood)).mono (by omega)
    have h2 : OrdGoodG (2 * r) (2 * E0Good.a₂ * t * w) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using h2base.nat_mul 2
    have h4 : OrdGoodG (2 * r) (E0Good.a₄ * w ^ 2) := by
      rw [pow_two]
      exact (c4.mul (hwGood.mul hwGood)).mono (by omega)
    dsimp [TN]
    exact ((h0.add h1).add h2).add h4
  let m : L := TN / TU
  have hmGood : OrdGoodG (2 * r) m :=
    hTN.div_unit hTUunit.1 hTUunit.2
  have hTUm : TU * m = TN := by
    dsimp [m]
    field_simp [hTUunit.1]
  let b : L := w - m * t
  have hline : w = m * t + b := by dsimp [b]; ring
  have hbGood : OrdGoodG (3 * r) b := by
    have hmt : OrdGoodG (3 * r) (m * t) :=
      (hmGood.mul htGood).mono (by omega)
    dsimp [b]
    exact hwGood.sub hmt
  let et : L := E0Good.a₁ * t + E0Good.a₃ * w - 2
  have hbIdentity : TU * b = w * et := by
    have hTUm' := hTUm
    dsimp [TU, TN] at hTUm'
    dsimp [b, et]
    simp only [GGood] at hG
    linear_combination 3 * hG - t * hTUm'
  have htwo : ordPi (2 : L) = 0 := by
    have hn1 : ordPi (-1 : L) = 0 := by rw [ordPi_neg, ordPi_one]
    calc
      ordPi (2 : L) = ordPi ((-1 : L) + 3) := by norm_num
      _ = ordPi (-1 : L) :=
        ordPi_add_eq_of_lt (by norm_num) (by norm_num)
          (by rw [hn1, ordPi_three]; omega)
      _ = 0 := hn1
  let qet : L := -(E0Good.a₁ * t + E0Good.a₃ * w) / 2
  have hqet : OrdGoodG 1 qet := by
    dsimp [qet]
    exact ((c1.mul ht1).mono (by omega) |>.add
      ((c3.mul hw1).mono (by omega))).neg.div_unit (by norm_num) htwo
  have hqetUnit : 1 + qet ≠ 0 ∧ ordPi (1 + qet) = 0 :=
    hqet.unit_one_add
  have hetEq : et = -2 * (1 + qet) := by
    dsimp [et, qet]
    field_simp
    ring
  have hetUnit : et ≠ 0 ∧ ordPi et = 0 := by
    constructor
    · rw [hetEq]
      exact mul_ne_zero (by norm_num) hqetUnit.1
    · rw [hetEq, ordPi_mul (by norm_num) hqetUnit.1,
        ordPi_neg, htwo, hqetUnit.2]
      omega
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, mul_zero] at hbIdentity
    exact (mul_ne_zero hw0 hetUnit.1) hbIdentity.symm
  let u : L := -BGood m b / AGood m - t - t
  let d : L := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
  let t₃ : L := -u / d
  have hval := line_valuation_good r t t m b hr htGood htGood hmGood hbGood
  change (AGood m ≠ 0 ∧ ordPi (AGood m) = 0) ∧
    (d ≠ 0 ∧ ordPi d = 0) ∧ OrdGoodG r u ∧
    (t₃ - t - t = 0 ∨ 2 * r ≤ ordPi (t₃ - t - t)) at hval
  rcases hval with ⟨hAunit, hdunit, huGood, herr⟩
  have hlineG : GGood t (m * t + b) = 0 := by rw [← hline]; exact hG
  have htangent :
      -3 * AGood m * t ^ 2 - 2 * BGood m b * t + CGood m b = 0 := by
    have hTUm' := hTUm
    dsimp [TU, TN] at hTUm'
    simp only [AGood, BGood, CGood]
    dsimp [b]
    linear_combination hTUm'
  have hsum : AGood m * (t + t + u) + BGood m b = 0 := by
    dsimp [u]
    field_simp [hAunit.1]
    ring
  have hpair :
      AGood m * (t * t + (t + t) * u) + CGood m b = 0 := by
    linear_combination htangent + 2 * t * hsum
  have hp := hlineG
  rw [GGood_line] at hp
  have hprod : AGood m * t * t * u = DGood b := by
    linear_combination -hp - t ^ 2 * hsum + t * hpair
  have hxsumData := vieta_x_sum_good m b t t u hAunit.1 hb0 hsum hpair hprod
  dsimp only at hxsumData
  rcases hxsumData with ⟨hqprod, hxsum⟩
  have hmu0 : m * u + b ≠ 0 := by
    intro h; apply hqprod; simp [h]
  have hmt0 : m * t + b ≠ 0 := by simpa only [← hline] using hw0
  have hxchart0 : x = t / w := by
    dsimp [t, w]; field_simp [hy0]
  have hychart0 : y = -1 / w := by
    dsimp [w]; field_simp [hy0]
  have hxchart : x = t / (m * t + b) := by rw [← hline]; exact hxchart0
  have hychart : y = -1 / (m * t + b) := by rw [← hline]; exact hychart0
  let ell := WeierstrassCurve.Affine.slope E0Good x x y y
  have hyne' : y ≠ WeierstrassCurve.Affine.negY E0Good x y := Ne.symm hyne
  have hellFormula : ell = TN / (w * et) := by
    dsimp only [ell]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne']
    rw [hxchart0, hychart0]
    simp only [WeierstrassCurve.Affine.negY]
    dsimp [TN, et]
    field_simp [hw0, hetUnit.1]
    ring
  have hell : ell = m / b := by
    rw [hellFormula]
    apply (div_eq_div_iff (mul_ne_zero hw0 hetUnit.1) hb0).2
    linear_combination -b * hTUm + m * hbIdentity
  let x₃ := WeierstrassCurve.Affine.addX E0Good x x ell
  have hx₃ : x₃ = u / (m * u + b) := by
    change ell ^ 2 + E0Good.a₁ * ell - E0Good.a₂ - x - x =
      u / (m * u + b)
    rw [hell, hxchart, ← hxsum]
    abel
  let ybar := WeierstrassCurve.Affine.negAddY E0Good x x y ell
  have hybar : ybar = -1 / (m * u + b) := by
    change ell * (x₃ - x) + y = -1 / (m * u + b)
    rw [hx₃, hell, hxchart, hychart]
    field_simp [hb0, hmt0, hmu0]
    ring
  let y₃ := WeierstrassCurve.Affine.addY E0Good x x y ell
  have hy₃ : y₃ = d / (m * u + b) := by
    change WeierstrassCurve.Affine.negY E0Good x₃ ybar = d / (m * u + b)
    rw [hybar, hx₃]
    simp only [WeierstrassCurve.Affine.negY]
    dsimp [d]
    field_simp [hmu0]
    ring
  have hbridge : MazurProof.N18PackageII.zParamGood (P + P) = t₃ := by
    dsimp [P]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne']
    change -x₃ / y₃ = t₃
    rw [hx₃, hy₃]
    dsimp [t₃]
    have hmu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hmu0
    field_simp [hmu0, hmu0', hdunit.1]
  have hmuGood : OrdGoodG (3 * r) (m * u) :=
    (hmGood.mul huGood).mono (by omega)
  have hmubGood : OrdGoodG (3 * r) (m * u + b) :=
    hmuGood.add hbGood
  have hmubOrd : 3 * r ≤ ordPi (m * u + b) := by
    rcases hmubGood with hmubZero | hmubOrd
    · exact (hmu0 hmubZero).elim
    · exact hmubOrd
  have hns₃ : WeierstrassCurve.Affine.Nonsingular E0Good x₃ y₃ := by
    exact WeierstrassCurve.Affine.nonsingular_add hns hns
      (fun hxy ↦ hyne' hxy.2)
  have hy₃v : ordPi y₃ = -ordPi (m * u + b) := by
    rw [hy₃, ordPi_div hdunit.1 hmu0, hdunit.2]
    ring
  have hy₃neg : ordPi y₃ < 0 := by
    rw [hy₃v]
    omega
  have hx₃neg : ordPi x₃ < 0 := by
    by_contra hx₃
    have hy₃nonneg := y_nonneg_of_x_nonneg_good hns₃ (le_of_not_gt hx₃)
    omega
  have hformal : InFormalKernel (P + P) := by
    dsimp only [P]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne']
    exact Or.inr hx₃neg
  dsimp only
  refine ⟨hformal, ?_⟩
  rw [hbridge]
  change t₃ - 2 * t = 0 ∨ 2 * r ≤ ordPi (t₃ - 2 * t)
  rw [show t₃ - 2 * t = t₃ - t - t by ring]
  exact herr

/-- Package I on the good model, in the weak form used by the induction.
The intended proof expands the integral chart law and applies the
ultrametric inequality term by term; every error monomial has total order at
least twice the smaller input order. -/
theorem add_congr_good_weak (P Q : GoodPoint)
    (hP : InFormalKernel P) (hQ : InFormalKernel Q) :
    2 * min
        (vpiGood (MazurProof.N18PackageII.zParamGood P))
        (vpiGood (MazurProof.N18PackageII.zParamGood Q)) ≤
      vpiGood
        (MazurProof.N18PackageII.zParamGood (P + Q) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood Q) := by
  rcases hP with hP0 | hPx
  · subst P
    have herr : MazurProof.N18PackageII.zParamGood ((0 : GoodPoint) + Q) -
        MazurProof.N18PackageII.zParamGood 0 -
        MazurProof.N18PackageII.zParamGood Q = 0 := by
      rw [zero_add Q, MazurProof.N18PackageII.zParamGood_zero]
      ring
    rw [herr, vpiGood_zero]
    exact le_top
  rcases hQ with hQ0 | hQx
  · subst Q
    have herr : MazurProof.N18PackageII.zParamGood (P + (0 : GoodPoint)) -
        MazurProof.N18PackageII.zParamGood P -
        MazurProof.N18PackageII.zParamGood 0 = 0 := by
      rw [add_zero P, MazurProof.N18PackageII.zParamGood_zero]
      ring
    rw [herr, vpiGood_zero]
    exact le_top
  rcases P with _ | ⟨x₁, y₁, hns₁⟩
  · simp [xCoordGood, ordPi_zero] at hPx
  rcases Q with _ | ⟨x₂, y₂, hns₂⟩
  · simp [xCoordGood, ordPi_zero] at hQx
  simp only [xCoordGood] at hPx hQx
  have hx₁0 : x₁ ≠ 0 := by
    intro h; rw [h, ordPi_zero] at hPx; omega
  have hx₂0 : x₂ ≠ 0 := by
    intro h; rw [h, ordPi_zero] at hQx; omega
  have hy₁0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₁ hPx
  have hy₂0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₂ hQx
  let P₁ : GoodPoint := .some x₁ y₁ hns₁
  let Q₂ : GoodPoint := .some x₂ y₂ hns₂
  have hzP : MazurProof.N18PackageII.zParamGood P₁ ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hx₁0) hy₁0
  have hzQ : MazurProof.N18PackageII.zParamGood Q₂ ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hx₂0) hy₂0
  have hzPpos : 1 ≤ ordPi (MazurProof.N18PackageII.zParamGood P₁) := by
    have hc := GoodModel.val_coords hx₁0 hy₁0
      (by simpa using (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hns₁.1) hPx
    dsimp [P₁, MazurProof.N18PackageII.zParamGood]
    omega
  have hzQpos : 1 ≤ ordPi (MazurProof.N18PackageII.zParamGood Q₂) := by
    have hc := GoodModel.val_coords hx₂0 hy₂0
      (by simpa using (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp hns₂.1) hQx
    dsimp [Q₂, MazurProof.N18PackageII.zParamGood]
    omega
  change 2 * min
      (vpiGood (MazurProof.N18PackageII.zParamGood P₁))
      (vpiGood (MazurProof.N18PackageII.zParamGood Q₂)) ≤
    vpiGood (MazurProof.N18PackageII.zParamGood (P₁ + Q₂) -
      MazurProof.N18PackageII.zParamGood P₁ -
      MazurProof.N18PackageII.zParamGood Q₂)
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = WeierstrassCurve.Affine.negY E0Good x₁ y₂
    · have hy₂ : y₂ = WeierstrassCurve.Affine.negY E0Good x₁ y₁ := by
        rw [hy, WeierstrassCurve.Affine.negY_negY]
      have hQnegP : Q₂ = -P₁ := by
        subst y₂
        dsimp only [P₁, Q₂]
        rfl
      rw [hQnegP]
      have hb := (add_congr_inverse_good hx₁0 hy₁0 hns₁ hPx).2
      let err := MazurProof.N18PackageII.zParamGood (P₁ + -P₁) -
        MazurProof.N18PackageII.zParamGood P₁ -
        MazurProof.N18PackageII.zParamGood (-P₁)
      change err = 0 ∨
        2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) ≤ ordPi err at hb
      rcases hb with herr | herr
      · change 2 * min
            (vpiGood (MazurProof.N18PackageII.zParamGood P₁))
            (vpiGood (MazurProof.N18PackageII.zParamGood (-P₁))) ≤
          vpiGood err
        rw [herr, vpiGood_zero]
        exact le_top
      · have herr0 : err ≠ 0 := by
          intro h
          rw [h, ordPi_zero] at herr
          omega
        have hvneg := vpi_zParamGood_neg P₁ (Or.inr hPx)
        rw [hvneg, min_self, vpiGood_apply_of_ne hzP,
          vpiGood_apply_of_ne herr0]
        change ((2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) : ℤ) :
          WithTop ℤ) ≤ (ordPi err : WithTop ℤ)
        exact WithTop.coe_le_coe.mpr herr
    · have hyEq : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 rfl hy
      subst y₂
      cases Subsingleton.elim hns₂ hns₁
      have hQP : Q₂ = P₁ := rfl
      rw [hQP]
      have hb :=
        (add_congr_tangent_good hx₁0 hy₁0 hns₁ hPx (fun h => hy h.symm)).2
      let err := MazurProof.N18PackageII.zParamGood (P₁ + P₁) -
        2 * MazurProof.N18PackageII.zParamGood P₁
      change err = 0 ∨
        2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) ≤ ordPi err at hb
      rcases hb with herr | herr
      · have herrShape :
            MazurProof.N18PackageII.zParamGood (P₁ + P₁) -
                MazurProof.N18PackageII.zParamGood P₁ -
                MazurProof.N18PackageII.zParamGood P₁ = err := by
          dsimp [err]
          ring
        rw [herrShape, herr, vpiGood_zero]
        exact le_top
      · have herr0 : err ≠ 0 := by
          intro h; rw [h, ordPi_zero] at herr; omega
        rw [min_self, vpiGood_apply_of_ne hzP,
          show MazurProof.N18PackageII.zParamGood (P₁ + P₁) -
              MazurProof.N18PackageII.zParamGood P₁ -
              MazurProof.N18PackageII.zParamGood P₁ = err by
            dsimp [err]; ring,
          vpiGood_apply_of_ne herr0]
        change ((2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) : ℤ) :
          WithTop ℤ) ≤ (ordPi err : WithTop ℤ)
        exact WithTop.coe_le_coe.mpr herr
  · have hb := (add_congr_distinct_good
      hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hx hPx hQx).2
    let err := MazurProof.N18PackageII.zParamGood (P₁ + Q₂) -
      MazurProof.N18PackageII.zParamGood P₁ -
      MazurProof.N18PackageII.zParamGood Q₂
    change err = 0 ∨
      2 * min (ordPi (MazurProof.N18PackageII.zParamGood P₁))
        (ordPi (MazurProof.N18PackageII.zParamGood Q₂)) ≤ ordPi err at hb
    rcases hb with herr | herr
    · change 2 * min
          (vpiGood (MazurProof.N18PackageII.zParamGood P₁))
          (vpiGood (MazurProof.N18PackageII.zParamGood Q₂)) ≤
        vpiGood err
      rw [herr, vpiGood_zero]
      exact le_top
    · have herr0 : err ≠ 0 := by
        intro h; rw [h, ordPi_zero] at herr; omega
      rw [vpiGood_apply_of_ne hzP, vpiGood_apply_of_ne hzQ,
        vpiGood_apply_of_ne herr0]
      change ((2 * min
          (ordPi (MazurProof.N18PackageII.zParamGood P₁))
          (ordPi (MazurProof.N18PackageII.zParamGood Q₂)) : ℤ) :
        WithTop ℤ) ≤ (ordPi err : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr herr

/-- The near-origin locus is closed under addition. -/
theorem kernel_add_closed_good (P Q : GoodPoint)
    (hP : InFormalKernel P) (hQ : InFormalKernel Q) :
    InFormalKernel (P + Q) := by
  rcases hP with hP0 | hPx
  · subst P
    rw [zero_add Q]
    exact hQ
  rcases hQ with hQ0 | hQx
  · subst Q
    rw [add_zero P]
    exact Or.inr hPx
  rcases P with _ | ⟨x₁, y₁, hns₁⟩
  · simp [xCoordGood, ordPi_zero] at hPx
  rcases Q with _ | ⟨x₂, y₂, hns₂⟩
  · simp [xCoordGood, ordPi_zero] at hQx
  simp only [xCoordGood] at hPx hQx
  have hx₁0 : x₁ ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hPx
    omega
  have hx₂0 : x₂ ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hQx
    omega
  have hy₁0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₁ hPx
  have hy₂0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₂ hQx
  let P₁ : GoodPoint := .some x₁ y₁ hns₁
  let Q₂ : GoodPoint := .some x₂ y₂ hns₂
  change InFormalKernel (P₁ + Q₂)
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = WeierstrassCurve.Affine.negY E0Good x₁ y₂
    · have hy₂ : y₂ = WeierstrassCurve.Affine.negY E0Good x₁ y₁ := by
        rw [hy, WeierstrassCurve.Affine.negY_negY]
      have hQnegP : Q₂ = -P₁ := by
        subst y₂
        rfl
      rw [hQnegP]
      exact (add_congr_inverse_good hx₁0 hy₁0 hns₁ hPx).1
    · have hyEq : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 rfl hy
      subst y₂
      cases Subsingleton.elim hns₂ hns₁
      have hQP : Q₂ = P₁ := rfl
      rw [hQP]
      exact (add_congr_tangent_good hx₁0 hy₁0 hns₁ hPx
        (fun h ↦ hy h.symm)).1
  · exact (add_congr_distinct_good
      hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hx hPx hQx).1

/-! ## Residue codes for the quotient by the formal kernel -/

abbrev GoodOL := NumberField.RingOfIntegers L

/-- Reduction modulo `pi` in the integral basis `1, pi, pi²`. -/
private def reducePiOL : GoodOL →+* ZMod 3 where
  toFun u := ((MazurProof.N18RouteC.LocalThreeSound.coordsOf u).c0 : ZMod 3)
  map_zero' := by
    simp [MazurProof.N18RouteC.LocalThreeSound.coordsOf_zero]
  map_one' := by
    simp [MazurProof.N18RouteC.LocalThreeSound.coordsOf_one,
      MazurProof.N18RouteC.LocalThreeSound.IntCoords.one]
  map_add' x y := by
    simp [MazurProof.N18RouteC.LocalThreeSound.coordsOf_add,
      MazurProof.N18RouteC.LocalThreeSound.IntCoords.add]
  map_mul' x y := by
    rw [MazurProof.N18RouteC.LocalThreeSound.coordsOf_mul]
    simp only [MazurProof.N18RouteC.LocalThreeSound.IntCoords.mul,
      MazurProof.N18RouteC.LocalThreeSound.prodC0]
    push_cast
    rw [show (3 : ZMod 3) = 0 by decide,
      show (9 : ZMod 3) = 0 by decide]
    ring

@[simp] private theorem reducePiOL_piInteger :
    reducePiOL FieldArithmetic.piInteger = 0 := by
  simp [reducePiOL, MazurProof.N18RouteC.LocalThreeSound.coordsOf_piInteger]

@[simp] private theorem reducePiOL_aInteger :
    reducePiOL FieldArithmetic.aInteger = 1 := by
  simp [reducePiOL, MazurProof.N18RouteC.LocalThreeSound.coordsOf_aInteger,
    MazurProof.N18RouteC.LocalThreeSound.aCoords]

@[simp] private theorem reducePiOL_natCast (n : ℕ) :
    reducePiOL (n : GoodOL) = (n : ZMod 3) :=
  map_natCast reducePiOL n

private theorem reducePiOL_den_ne_zero (d : p3.asIdeal.primeCompl) :
    reducePiOL d ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  have hd := MazurProof.N18RouteC.LocalThreeSound.reduceOL_isUnit_of_not_mem d.prop
  rw [MazurProof.N18RouteC.LocalThree.isUnit5_iff] at hd
  exact isUnit_iff_ne_zero.mpr (by
    simpa [reducePiOL, MazurProof.N18RouteC.LocalThreeSound.reduceOL,
      MazurProof.N18RouteC.LocalThreeSound.IntCoords.red,
      MazurProof.N18RouteC.LocalThreeSound.reduceInt,
      MazurProof.N18RouteC.LocalThree.red3] using hd)

private def IntegralAtPi (x : L) : Prop := p3.valuation L x ≤ 1

private def ReducesPi (x : L) (r : ZMod 3) : Prop :=
  ∃ n : GoodOL, ∃ d : p3.asIdeal.primeCompl,
    x * algebraMap GoodOL L d = algebraMap GoodOL L n ∧
      r * reducePiOL d = reducePiOL n

private theorem reducesPi_exists {x : L} (hx : IntegralAtPi x) :
    ∃ r : ZMod 3, ReducesPi x r := by
  obtain ⟨n, d, hnd⟩ := p3.exists_primeCompl_mul_eq_of_integer x hx
  refine ⟨reducePiOL n / reducePiOL d, n, d, hnd, ?_⟩
  exact div_mul_cancel₀ _ (reducePiOL_den_ne_zero d)

private theorem reducesPi_unique {x : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi x s) : r = s := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  have hcrossL :
      algebraMap GoodOL L (n * d') = algebraMap GoodOL L (n' * d) := by
    simp only [map_mul]
    calc
      algebraMap GoodOL L n * algebraMap GoodOL L (d' : GoodOL) =
          (x * algebraMap GoodOL L (d : GoodOL)) *
            algebraMap GoodOL L (d' : GoodOL) := by rw [hxd]
      _ = (x * algebraMap GoodOL L (d' : GoodOL)) *
            algebraMap GoodOL L (d : GoodOL) := by ring
      _ = algebraMap GoodOL L n' * algebraMap GoodOL L (d : GoodOL) := by
        rw [hxd']
  have hcross : n * (d' : GoodOL) = n' * (d : GoodOL) :=
    (FaithfulSMul.algebraMap_injective GoodOL L) hcrossL
  apply mul_right_cancel₀
    (mul_ne_zero (reducePiOL_den_ne_zero d) (reducePiOL_den_ne_zero d'))
  calc
    r * (reducePiOL d * reducePiOL d') =
        (r * reducePiOL d) * reducePiOL d' := by ring
    _ = reducePiOL n * reducePiOL d' := by rw [hrd]
    _ = reducePiOL (n * (d' : GoodOL)) := by rw [map_mul]
    _ = reducePiOL (n' * (d : GoodOL)) := by rw [hcross]
    _ = reducePiOL n' * reducePiOL d := by rw [map_mul]
    _ = (s * reducePiOL d') * reducePiOL d := by rw [hsd']
    _ = s * (reducePiOL d * reducePiOL d') := by ring

private theorem integralAtPi_zero : IntegralAtPi (0 : L) := by
  simp [IntegralAtPi]

private theorem IntegralAtPi.add {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x + y) := by
  exact (p3.valuation L).map_add x y |>.trans (max_le hx hy)

private theorem IntegralAtPi.neg {x : L} (hx : IntegralAtPi x) :
    IntegralAtPi (-x) := by
  simpa [IntegralAtPi] using hx

private theorem IntegralAtPi.sub {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

private theorem IntegralAtPi.mul {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x * y) := by
  unfold IntegralAtPi at hx hy ⊢
  rw [map_mul]
  exact (mul_le_mul' hx hy).trans_eq (mul_one 1)

private theorem IntegralAtPi.pow {x : L} (hx : IntegralAtPi x) (n : ℕ) :
    IntegralAtPi (x ^ n) := by
  induction n with
  | zero => simp [IntegralAtPi]
  | succ n ih => simpa [pow_succ] using ih.mul hx

private theorem ReducesPi.zero : ReducesPi (0 : L) 0 := by
  refine ⟨0, 1, ?_, ?_⟩
  · simp
  · rw [map_zero]
    simp

private theorem ReducesPi.add {x y : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi y s) :
    ReducesPi (x + y) (r + s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * (d' : GoodOL) + n' * (d : GoodOL), d * d', ?_, ?_⟩
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (x + y) * (algebraMap GoodOL L d * algebraMap GoodOL L d') =
          (x * algebraMap GoodOL L d) * algebraMap GoodOL L d' +
            (y * algebraMap GoodOL L d') * algebraMap GoodOL L d := by ring
      _ = algebraMap GoodOL L n * algebraMap GoodOL L d' +
            algebraMap GoodOL L n' * algebraMap GoodOL L d := by rw [hxd, hxd']
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (r + s) * (reducePiOL d * reducePiOL d') =
          (r * reducePiOL d) * reducePiOL d' +
            (s * reducePiOL d') * reducePiOL d := by ring
      _ = reducePiOL n * reducePiOL d' +
            reducePiOL n' * reducePiOL d := by rw [hrd, hsd']

private theorem ReducesPi.neg {x : L} {r : ZMod 3}
    (hr : ReducesPi x r) : ReducesPi (-x) (-r) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  refine ⟨-n, d, ?_, ?_⟩
  · simp only [map_neg]
    linear_combination -hxd
  · simp only [map_neg]
    linear_combination -hrd

private theorem ReducesPi.sub {x y : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi y s) :
    ReducesPi (x - y) (r - s) := by
  simpa [sub_eq_add_neg] using hr.add hs.neg

private theorem ReducesPi.mul {x y : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi y s) :
    ReducesPi (x * y) (r * s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * n', d * d', ?_, ?_⟩
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hxd, ← hxd']
    ring
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hrd, ← hsd']
    ring

private theorem ReducesPi.pow {x : L} {r : ZMod 3}
    (hr : ReducesPi x r) (n : ℕ) : ReducesPi (x ^ n) (r ^ n) := by
  induction n with
  | zero =>
      refine ⟨1, 1, ?_, ?_⟩ <;> simp [reducePiOL]
  | succ n ih => simpa [pow_succ] using ih.mul hr

private theorem reducesPi_existsUnique {x : L} (hx : IntegralAtPi x) :
    ∃! r : ZMod 3, ReducesPi x r := by
  obtain ⟨r, hr⟩ := reducesPi_exists hx
  exact ⟨r, hr, fun s hs ↦ (reducesPi_unique hr hs).symm⟩

private noncomputable def reducePi (x : L) (hx : IntegralAtPi x) : ZMod 3 :=
  Classical.choose (reducesPi_existsUnique hx)

private theorem reducePi_spec (x : L) (hx : IntegralAtPi x) :
    ReducesPi x (reducePi x hx) :=
  (Classical.choose_spec (reducesPi_existsUnique hx)).1

private theorem reducePi_eq_of_reduces {x : L} (hx : IntegralAtPi x)
    {r : ZMod 3} (hr : ReducesPi x r) : reducePi x hx = r :=
  reducesPi_unique (reducePi_spec x hx) hr

@[simp] private theorem reducePi_zero :
    reducePi 0 integralAtPi_zero = 0 :=
  reducePi_eq_of_reduces integralAtPi_zero ReducesPi.zero

private theorem reducePi_add {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reducePi (x + y) (hx.add hy) = reducePi x hx + reducePi y hy :=
  reducePi_eq_of_reduces (hx.add hy) ((reducePi_spec x hx).add (reducePi_spec y hy))

private theorem reducePi_neg {x : L} (hx : IntegralAtPi x) :
    reducePi (-x) hx.neg = -reducePi x hx :=
  reducePi_eq_of_reduces hx.neg (reducePi_spec x hx).neg

private theorem reducePi_sub {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reducePi (x - y) (hx.sub hy) = reducePi x hx - reducePi y hy :=
  reducePi_eq_of_reduces (hx.sub hy)
    ((reducePi_spec x hx).sub (reducePi_spec y hy))

private theorem reducePi_mul {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reducePi (x * y) (hx.mul hy) = reducePi x hx * reducePi y hy :=
  reducePi_eq_of_reduces (hx.mul hy)
    ((reducePi_spec x hx).mul (reducePi_spec y hy))

private theorem reducePi_pow {x : L} (hx : IntegralAtPi x) (n : ℕ) :
    reducePi (x ^ n) (hx.pow n) = reducePi x hx ^ n :=
  reducePi_eq_of_reduces (hx.pow n) ((reducePi_spec x hx).pow n)

private theorem reducePi_of_integer (n : GoodOL) :
    reducePi (algebraMap GoodOL L n) (by
      simpa [IntegralAtPi] using p3.valuation_le_one (K := L) n) = reducePiOL n := by
  apply reducePi_eq_of_reduces
  refine ⟨n, 1, ?_, ?_⟩ <;> simp

private theorem valuation_eq_exp_neg_ordPi {x : L} (hx : x ≠ 0) :
    p3.valuation L x = WithZero.exp (-ordPi x) := by
  have hv : p3.valuation L x ≠ 0 :=
    (Valuation.ne_zero_iff (p3.valuation L)).2 hx
  calc
    p3.valuation L x = WithZero.exp (WithZero.log (p3.valuation L x)) :=
      (WithZero.exp_log hv).symm
    _ = WithZero.exp (-ordPi x) := by
      congr 1
      simp [ordPi, v3]

private theorem integralAtPi_of_ordPi_nonneg {x : L} (hx : x ≠ 0)
    (hord : 0 ≤ ordPi x) : IntegralAtPi x := by
  unfold IntegralAtPi
  rw [valuation_eq_exp_neg_ordPi hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

private theorem reducePi_eq_zero_of_ordPi_pos {x : L} (hx : x ≠ 0)
    (hord : 0 < ordPi x) :
    reducePi x (integralAtPi_of_ordPi_nonneg hx hord.le) = 0 := by
  let hxInt := integralAtPi_of_ordPi_nonneg hx hord.le
  obtain ⟨n, d, hxd, hred⟩ := reducePi_spec x hxInt
  have hdL : algebraMap GoodOL L (d : GoodOL) ≠ 0 :=
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective GoodOL L)).not.mpr
      (fun hd ↦ d.property (hd ▸ Submodule.zero_mem _))
  have hdord : ordPi (algebraMap GoodOL L (d : GoodOL)) = 0 := by
    have hv : p3.valuation L (algebraMap GoodOL L (d : GoodOL)) = 1 :=
      (p3.valuation_eq_one_iff_notMem (K := L)).2 d.property
    simp [ordPi, v3, hv]
  have hnL : algebraMap GoodOL L n ≠ 0 := by
    rw [← hxd]
    exact mul_ne_zero hx hdL
  have hnord : ordPi (algebraMap GoodOL L n) = ordPi x := by
    rw [← hxd, ordPi_mul hx hdL, hdord, add_zero]
  have hnmem : n ∈ p3.asIdeal := by
    by_contra hnmem
    have hv : p3.valuation L (algebraMap GoodOL L n) = 1 :=
      (p3.valuation_eq_one_iff_notMem (K := L)).2 hnmem
    have hz : ordPi (algebraMap GoodOL L n) = 0 := by
      simp [ordPi, v3, hv]
    rw [hnord] at hz
    omega
  have hnbar : reducePiOL n = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (by
      simpa [p3, primeAboveThree_eq_span_pi] using hnmem)
    rw [hc, map_mul, reducePiOL_piInteger, zero_mul]
  rw [hnbar] at hred
  exact (mul_eq_zero.mp hred).resolve_right (reducePiOL_den_ne_zero d)

private theorem reducePi_ne_zero_of_ordPi_eq_zero {x : L} (hx : x ≠ 0)
    (hord : ordPi x = 0) :
    reducePi x (integralAtPi_of_ordPi_nonneg hx hord.ge) ≠ 0 := by
  let hxInt := integralAtPi_of_ordPi_nonneg hx hord.ge
  have hvx : p3.valuation L x = 1 := by
    rw [valuation_eq_exp_neg_ordPi hx, hord]
    simp
  have hxInvInt : IntegralAtPi x⁻¹ := by
    unfold IntegralAtPi
    rw [map_inv₀, hvx, inv_one]
  let r := reducePi x hxInt
  let s := reducePi x⁻¹ hxInvInt
  have hrs : ReducesPi (1 : L) (r * s) := by
    obtain ⟨n, d, hxd, hrd⟩ := reducePi_spec x hxInt
    obtain ⟨n', d', hxd', hrd'⟩ := reducePi_spec x⁻¹ hxInvInt
    refine ⟨n * n', d * d', ?_, ?_⟩
    · simp only [map_mul, Submonoid.coe_mul]
      rw [← hxd, ← hxd']
      field_simp [hx]
    · simp only [map_mul, Submonoid.coe_mul]
      rw [← hrd, ← hrd']
      ring
  have hone : ReducesPi (1 : L) 1 := by
    refine ⟨1, 1, ?_, ?_⟩ <;> simp [reducePiOL]
  have hrsOne : r * s = 1 := reducesPi_unique hrs hone
  intro hr0
  change r = 0 at hr0
  rw [hr0, zero_mul] at hrsOne
  exact zero_ne_one hrsOne

private theorem integralAtPi_of_ordPi_nonneg_total {x : L}
    (hx : 0 ≤ ordPi x) : IntegralAtPi x := by
  by_cases hx0 : x = 0
  · subst x
    exact integralAtPi_zero
  · exact integralAtPi_of_ordPi_nonneg hx0 hx

private noncomputable def reduceNonneg (x : L) (hx : 0 ≤ ordPi x) : ZMod 3 :=
  reducePi x (integralAtPi_of_ordPi_nonneg_total hx)

private theorem reduceNonneg_sub {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y)
    (hxy : 0 ≤ ordPi (x - y)) :
    reduceNonneg (x - y) hxy = reduceNonneg x hx - reduceNonneg y hy := by
  unfold reduceNonneg
  simpa only using reducePi_sub
    (integralAtPi_of_ordPi_nonneg_total hx)
    (integralAtPi_of_ordPi_nonneg_total hy)

private theorem reduceNonneg_add {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y)
    (hxy : 0 ≤ ordPi (x + y)) :
    reduceNonneg (x + y) hxy = reduceNonneg x hx + reduceNonneg y hy := by
  unfold reduceNonneg
  simpa only using reducePi_add
    (integralAtPi_of_ordPi_nonneg_total hx)
    (integralAtPi_of_ordPi_nonneg_total hy)

private theorem reduceNonneg_neg {x : L}
    (hx : 0 ≤ ordPi x) (hnx : 0 ≤ ordPi (-x)) :
    reduceNonneg (-x) hnx = -reduceNonneg x hx := by
  unfold reduceNonneg
  simpa only using reducePi_neg (integralAtPi_of_ordPi_nonneg_total hx)

private theorem reduceNonneg_mul {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y)
    (hxy : 0 ≤ ordPi (x * y)) :
    reduceNonneg (x * y) hxy = reduceNonneg x hx * reduceNonneg y hy := by
  unfold reduceNonneg
  simpa only using reducePi_mul
    (integralAtPi_of_ordPi_nonneg_total hx)
    (integralAtPi_of_ordPi_nonneg_total hy)

private theorem reduceNonneg_pow {x : L}
    (hx : 0 ≤ ordPi x) (n : ℕ) (hxn : 0 ≤ ordPi (x ^ n)) :
    reduceNonneg (x ^ n) hxn = reduceNonneg x hx ^ n := by
  unfold reduceNonneg
  simpa only using reducePi_pow (integralAtPi_of_ordPi_nonneg_total hx) n

private theorem reduceNonneg_eq_zero_of_pos {x : L} (hx : x ≠ 0)
    (hord : 0 < ordPi x) :
    reduceNonneg x hord.le = 0 := by
  unfold reduceNonneg
  simpa only using reducePi_eq_zero_of_ordPi_pos hx hord

private theorem reduceNonneg_ne_zero_of_ord_eq_zero {x : L} (hx : x ≠ 0)
    (hord : ordPi x = 0) :
    reduceNonneg x hord.ge ≠ 0 := by
  unfold reduceNonneg
  simpa only using reducePi_ne_zero_of_ordPi_eq_zero hx hord

private theorem reduceNonneg_eq_of_eq {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) (hxy : x = y) :
    reduceNonneg x hx = reduceNonneg y hy := by
  subst y
  rfl

private theorem reduceNonneg_good_a₁ :
    reduceNonneg E0Good.a₁ good_coeff_orders.1 = 2 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₁)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₁] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₁
  calc
    reduceNonneg E0Good.a₁ good_coeff_orders.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₁) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₁ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 2 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₂ :
    reduceNonneg E0Good.a₂ good_coeff_orders.2.1 = 2 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₂)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₂] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₂
  calc
    reduceNonneg E0Good.a₂ good_coeff_orders.2.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₂) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₂ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 2 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₃ :
    reduceNonneg E0Good.a₃ good_coeff_orders.2.2.1 = 2 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₃)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₃] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₃
  calc
    reduceNonneg E0Good.a₃ good_coeff_orders.2.2.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₃) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₃ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 2 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₄ :
    reduceNonneg E0Good.a₄ good_coeff_orders.2.2.2.1 = 0 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₄)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₄] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₄
  calc
    reduceNonneg E0Good.a₄ good_coeff_orders.2.2.2.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₄) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₄ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 0 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₆ :
    reduceNonneg E0Good.a₆ good_coeff_orders.2.2.2.2 = 0 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₆)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₆] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₆
  calc
    reduceNonneg E0Good.a₆ good_coeff_orders.2.2.2.2 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₆) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₆ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 0 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reducesPi_nonneg {x : L} (hx : 0 ≤ ordPi x) :
    ReducesPi x (reduceNonneg x hx) := by
  unfold reduceNonneg
  exact reducePi_spec _ _

private theorem residue_equation_good {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    WeierstrassCurve.Affine.Equation reducedGoodCurve
      (reduceNonneg x hx) (reduceNonneg y hy) := by
  let rx := reduceNonneg x hx
  let ry := reduceNonneg y hy
  have hxRed : ReducesPi x rx := reducesPi_nonneg hx
  have hyRed : ReducesPi y ry := reducesPi_nonneg hy
  have ha₁Red : ReducesPi E0Good.a₁ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.1
    rwa [reduceNonneg_good_a₁] at hred
  have ha₂Red : ReducesPi E0Good.a₂ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.1
    rwa [reduceNonneg_good_a₂] at hred
  have ha₃Red : ReducesPi E0Good.a₃ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.1
    rwa [reduceNonneg_good_a₃] at hred
  have ha₄Red : ReducesPi E0Good.a₄ 0 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.2.1
    rwa [reduceNonneg_good_a₄] at hred
  have ha₆Red : ReducesPi E0Good.a₆ 0 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.2.2
    rwa [reduceNonneg_good_a₆] at hred
  have hlhs : ReducesPi
      (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y)
      (ry ^ 2 + 2 * rx * ry + 2 * ry) := by
    exact ((hyRed.pow 2).add ((ha₁Red.mul hxRed).mul hyRed)).add
      (ha₃Red.mul hyRed)
  have hrhs : ReducesPi
      (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆)
      (rx ^ 3 + 2 * rx ^ 2 + 0 * rx + 0) := by
    exact ((hxRed.pow 3).add (ha₂Red.mul (hxRed.pow 2))).add
      (ha₄Red.mul hxRed) |>.add ha₆Red
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  rw [heq] at hlhs
  have hred := reducesPi_unique hlhs hrhs
  simpa [rx, ry, reducedGoodCurve,
    WeierstrassCurve.Affine.equation_iff] using hred

private theorem redPoint_ne_neg_of_ne_zero
    (R : MazurProof.N18RouteC.Reduction.RedPoint) (hR : R ≠ 0) :
    R ≠ -R := by
  intro hself
  have htwo : (2 : ℕ) • R = 0 := by
    rw [two_nsmul]
    calc
      R + R = R + -R := congrArg (R + ·) hself
      _ = 0 := add_neg_cancel R
  have hordTwo : addOrderOf R ∣ 2 :=
    addOrderOf_dvd_of_nsmul_eq_zero htwo
  have hordSeven : addOrderOf R ∣ 7 :=
    addOrderOf_dvd_of_nsmul_eq_zero
      (MazurProof.N18RouteC.Reduction.seven_nsmul R)
  have hordOne : addOrderOf R = 1 := by
    apply Nat.dvd_one.mp
    simpa using Nat.dvd_gcd hordTwo hordSeven
  rw [AddMonoid.addOrderOf_eq_one_iff] at hordOne
  exact hR hordOne

private theorem reduced_pair_not_self_neg {x y : ZMod 3}
    (h : WeierstrassCurve.Affine.Equation reducedGoodCurve x y) :
    y ≠ WeierstrassCurve.Affine.negY reducedGoodCurve x y := by
  let R : MazurProof.N18RouteC.Reduction.RedPoint :=
    WeierstrassCurve.Affine.Point.mk h
  have hR0 : R ≠ 0 := by
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hRneg := redPoint_ne_neg_of_ne_zero R hR0
  intro hy
  apply hRneg
  change WeierstrassCurve.Affine.Point.some x y _ =
    WeierstrassCurve.Affine.Point.some x
      (WeierstrassCurve.Affine.negY reducedGoodCurve x y) _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, hy⟩

private theorem reduce_negY_good {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    ∃ hny : 0 ≤ ordPi (WeierstrassCurve.Affine.negY E0Good x y),
      reduceNonneg (WeierstrassCurve.Affine.negY E0Good x y) hny =
        WeierstrassCurve.Affine.negY reducedGoodCurve
          (reduceNonneg x hx) (reduceNonneg y hy) := by
  let ny := WeierstrassCurve.Affine.negY E0Good x y
  have hnonsing : WeierstrassCurve.Affine.Nonsingular E0Good x ny :=
    (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
  have hny : 0 ≤ ordPi ny := y_nonneg_of_x_nonneg_good hnonsing hx
  refine ⟨hny, ?_⟩
  have hxRed := reducesPi_nonneg hx
  have hyRed := reducesPi_nonneg hy
  have ha₁Red : ReducesPi E0Good.a₁ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.1
    rwa [reduceNonneg_good_a₁] at hred
  have ha₃Red : ReducesPi E0Good.a₃ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.1
    rwa [reduceNonneg_good_a₃] at hred
  have hformula : ReducesPi ny
      (-reduceNonneg y hy - 2 * reduceNonneg x hx - 2) := by
    simpa only [ny, WeierstrassCurve.Affine.negY] using
      (hyRed.neg.sub (ha₁Red.mul hxRed)).sub ha₃Red
  have hunique := reducesPi_unique (reducesPi_nonneg hny) hformula
  simpa only [ny, WeierstrassCurve.Affine.negY, reducedGoodCurve] using hunique

private noncomputable def residueCode :
    GoodPoint → Option (ZMod 3 × ZMod 3)
  | .zero => none
  | .some x y h =>
      if hx : ordPi x < 0 then none
      else
        let hx' := le_of_not_gt hx
        let hy' := y_nonneg_of_x_nonneg_good h hx'
        some (reduceNonneg x hx', reduceNonneg y hy')

private theorem formal_neg_good (P : GoodPoint)
    (hP : InFormalKernel P) : InFormalKernel (-P) := by
  rcases hP with rfl | hP
  · exact Or.inl rfl
  · exact Or.inr (by rwa [xCoordGood_neg])

private theorem residueCode_eq_none_iff (P : GoodPoint) :
    residueCode P = none ↔ InFormalKernel P := by
  cases P with
  | zero => exact iff_of_true rfl (Or.inl rfl)
  | some x y h =>
      simp [residueCode, InFormalKernel, xCoordGood]

private theorem formal_sub_of_residueCode_eq (P Q : GoodPoint)
    (hcode : residueCode P = residueCode Q) :
    InFormalKernel (P - Q) := by
  cases P with
  | zero =>
      have hQ : InFormalKernel Q := by
        apply (residueCode_eq_none_iff Q).mp
        simpa [residueCode] using hcode.symm
      rw [show WeierstrassCurve.Affine.Point.zero - Q = -Q by rfl]
      exact formal_neg_good Q hQ
  | some x₁ y₁ h₁ =>
      by_cases hx₁neg : ordPi x₁ < 0
      · have hP : InFormalKernel
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := Or.inr hx₁neg
        have hQ : InFormalKernel Q := by
          apply (residueCode_eq_none_iff Q).mp
          rw [← hcode]
          simp [residueCode, hx₁neg]
        simpa only [sub_eq_add_neg] using
          kernel_add_closed_good _ _ hP (formal_neg_good Q hQ)
      · have hx₁ : 0 ≤ ordPi x₁ := le_of_not_gt hx₁neg
        have hy₁ : 0 ≤ ordPi y₁ := y_nonneg_of_x_nonneg_good h₁ hx₁
        cases Q with
        | zero =>
            have : False := by
              have hc : residueCode
                  (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) ≠ none := by
                simp [residueCode, hx₁neg]
              exact hc (by simpa [residueCode] using hcode)
            exact this.elim
        | some x₂ y₂ h₂ =>
            by_cases hx₂neg : ordPi x₂ < 0
            · have : False := by
                have hc : residueCode
                    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) ≠ none := by
                  simp [residueCode, hx₁neg]
                apply hc
                rw [hcode]
                simp [residueCode, hx₂neg]
              exact this.elim
            · have hx₂ : 0 ≤ ordPi x₂ := le_of_not_gt hx₂neg
              have hy₂ : 0 ≤ ordPi y₂ := y_nonneg_of_x_nonneg_good h₂ hx₂
              have hcode' :
                  some (reduceNonneg x₁ hx₁, reduceNonneg y₁ hy₁) =
                    some (reduceNonneg x₂ hx₂, reduceNonneg y₂ hy₂) := by
                simpa only [residueCode, dif_neg hx₁neg, dif_neg hx₂neg] using hcode
              have hpair := Option.some.inj hcode'
              have hxred : reduceNonneg x₁ hx₁ = reduceNonneg x₂ hx₂ :=
                congrArg Prod.fst hpair
              have hyred : reduceNonneg y₁ hy₁ = reduceNonneg y₂ hy₂ :=
                congrArg Prod.snd hpair
              by_cases hxEq : x₁ = x₂
              · by_cases hyEq : y₁ = y₂
                · subst x₂
                  subst y₂
                  cases Subsingleton.elim h₂ h₁
                  exact Or.inl (sub_self _)
                · have hyNeg : y₁ = WeierstrassCurve.Affine.negY E0Good x₂ y₂ :=
                    (WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hxEq).resolve_left hyEq
                  obtain ⟨hny₂, hnyred⟩ := reduce_negY_good h₂ hx₂ hy₂
                  have hredEq : reduceNonneg y₁ hy₁ =
                      WeierstrassCurve.Affine.negY reducedGoodCurve
                        (reduceNonneg x₁ hx₁) (reduceNonneg y₁ hy₁) := by
                    calc
                      reduceNonneg y₁ hy₁ = reduceNonneg
                          (WeierstrassCurve.Affine.negY E0Good x₂ y₂) hny₂ :=
                        reduceNonneg_eq_of_eq _ _ hyNeg
                      _ = WeierstrassCurve.Affine.negY reducedGoodCurve
                          (reduceNonneg x₂ hx₂) (reduceNonneg y₂ hy₂) := hnyred
                      _ = WeierstrassCurve.Affine.negY reducedGoodCurve
                          (reduceNonneg x₁ hx₁) (reduceNonneg y₁ hy₁) := by
                        rw [hxred, hyred]
                  exact (reduced_pair_not_self_neg
                    (residue_equation_good h₁ hx₁ hy₁) hredEq).elim
              · let ny₂ := WeierstrassCurve.Affine.negY E0Good x₂ y₂
                obtain ⟨hny₂, hnyred⟩ := reduce_negY_good h₂ hx₂ hy₂
                let num := y₁ - ny₂
                let den := x₁ - x₂
                have hden0 : den ≠ 0 := sub_ne_zero.mpr hxEq
                have hden : 0 ≤ ordPi den := by
                  dsimp only [den]
                  have hnx₂ : 0 ≤ ordPi (-x₂) := by rwa [ordPi_neg]
                  simpa only [sub_eq_add_neg] using le_ordPi_add hx₁ hnx₂ le_rfl
                have hdenRed : reduceNonneg den hden = 0 := by
                  rw [reduceNonneg_sub hx₁ hx₂ hden, hxred, sub_self]
                have hdenPos : 0 < ordPi den := by
                  by_contra hpos
                  have hzero : ordPi den = 0 := by omega
                  exact (reduceNonneg_ne_zero_of_ord_eq_zero hden0 hzero)
                    (by simpa only [hzero] using hdenRed)
                have hnum : 0 ≤ ordPi num := by
                  dsimp only [num]
                  have hnny₂ : 0 ≤ ordPi (-ny₂) := by rwa [ordPi_neg]
                  simpa only [sub_eq_add_neg] using le_ordPi_add hy₁ hnny₂ le_rfl
                have hnumRed : reduceNonneg num hnum =
                    reduceNonneg y₁ hy₁ -
                      WeierstrassCurve.Affine.negY reducedGoodCurve
                        (reduceNonneg x₂ hx₂) (reduceNonneg y₂ hy₂) := by
                  rw [reduceNonneg_sub hy₁ hny₂ hnum, hnyred]
                have hnumRed0 : reduceNonneg num hnum ≠ 0 := by
                  rw [hnumRed]
                  intro hz
                  have hself : reduceNonneg y₁ hy₁ =
                      WeierstrassCurve.Affine.negY reducedGoodCurve
                        (reduceNonneg x₁ hx₁) (reduceNonneg y₁ hy₁) := by
                    have := sub_eq_zero.mp hz
                    simpa only [hxred, hyred] using this
                  exact reduced_pair_not_self_neg
                    (residue_equation_good h₁ hx₁ hy₁) hself
                have hnum0 : num ≠ 0 := by
                  intro hz
                  have hzeroOrd : 0 ≤ ordPi (0 : L) := by simp [ordPi_zero]
                  have hredEq := reduceNonneg_eq_of_eq hnum hzeroOrd hz
                  apply hnumRed0
                  rw [hredEq]
                  unfold reduceNonneg
                  simpa only using reducePi_zero
                have hnumOrd : ordPi num = 0 := by
                  by_contra hne
                  have hpos : 0 < ordPi num := by omega
                  exact hnumRed0 (by
                    simpa only using reduceNonneg_eq_zero_of_pos hnum0 hpos)
                let ell := WeierstrassCurve.Affine.slope E0Good x₁ x₂ y₁ ny₂
                have hell : ell = num / den := by
                  dsimp only [ell, num, den]
                  rw [WeierstrassCurve.Affine.slope_of_X_ne hxEq]
                have hell0 : ell ≠ 0 := by
                  rw [hell]
                  exact div_ne_zero hnum0 hden0
                have hellOrd : ordPi ell = -ordPi den := by
                  rw [hell, ordPi_div hnum0 hden0, hnumOrd]
                  omega
                have hellNeg : ordPi ell < 0 := by rw [hellOrd]; omega
                let tail := E0Good.a₁ * ell - E0Good.a₂ - x₁ - x₂
                have htail : ordPi ell ≤ ordPi tail := by
                  have h1 : ordPi ell ≤ ordPi (E0Good.a₁ * ell) :=
                    ordPi_le_mul_right_good good_coeff_orders.1 hellNeg.le
                  have h2 : ordPi ell ≤ ordPi (-E0Good.a₂) := by
                    have ha₂ := good_coeff_orders.2.1
                    rw [ordPi_neg]
                    omega
                  have h3 : ordPi ell ≤ ordPi (-x₁) := by
                    rw [ordPi_neg]
                    omega
                  have h4 : ordPi ell ≤ ordPi (-x₂) := by
                    rw [ordPi_neg]
                    omega
                  dsimp only [tail]
                  simpa only [sub_eq_add_neg] using
                    le_ordPi_add (le_ordPi_add (le_ordPi_add h1 h2 hellNeg.le)
                      h3 hellNeg.le) h4 hellNeg.le
                let x₃ := WeierstrassCurve.Affine.addX E0Good x₁ x₂ ell
                have hx₃Eq : x₃ = ell ^ 2 + tail := by
                  simp only [x₃, tail, WeierstrassCurve.Affine.addX]
                  ring
                have hellSq0 : ell ^ 2 ≠ 0 := pow_ne_zero 2 hell0
                have hellSqOrd : ordPi (ell ^ 2) = 2 * ordPi ell := by
                  rw [pow_two, ordPi_mul hell0 hell0]
                  ring
                have hx₃Ord : ordPi x₃ = 2 * ordPi ell := by
                  rw [hx₃Eq]
                  by_cases ht0 : tail = 0
                  · simp [ht0, hellSqOrd]
                  · exact (ordPi_add_eq_of_lt hellSq0 ht0 (by
                      rw [hellSqOrd]
                      omega)).trans hellSqOrd
                have hx₃Neg : ordPi x₃ < 0 := by rw [hx₃Ord]; omega
                rw [sub_eq_add_neg,
                  WeierstrassCurve.Affine.Point.neg_some,
                  WeierstrassCurve.Affine.Point.add_of_X_ne hxEq]
                exact Or.inr hx₃Neg

-- The quotient construction of the reduction homomorphism is below.

/-- The reduction homomorphism selected from `exists_good_reduction`. -/
noncomputable def redGood :
    GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint :=
  Classical.choose exists_good_reduction

theorem redGood_ker (P : GoodPoint) :
    P ∈ redGood.ker ↔ InFormalKernel P :=
  Classical.choose_spec exists_good_reduction P

/-- Supersingular connectedness puts every three-primary torsion point in the
kernel of good reduction.  This is the remaining Package III reduction fact. -/
theorem three_pow_torsion_mem_kernel_good (P : GoodPoint)
    (hP : ∃ k : ℕ, ((3 : ℤ) ^ k) • P = 0) :
    InFormalKernel P := by
  obtain ⟨k, hk⟩ := hP
  have hpow : ((3 : ℤ) ^ k) • redGood P = 0 := by
    rw [← map_zsmul, hk, map_zero]
  have hseven : (7 : ℤ) • redGood P = 0 :=
    MazurProof.N18ReductionHom.seven_zsmul_redPoint (redGood P)
  have hcop : IsCoprime ((3 : ℤ) ^ k) 7 :=
    (show IsCoprime (3 : ℤ) 7 by norm_num).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hred : redGood P = 0 := by
    calc
      redGood P = (1 : ℤ) • redGood P := by simp
      _ = (u * (3 : ℤ) ^ k + v * 7) • redGood P := by rw [huv]
      _ = u • (((3 : ℤ) ^ k) • redGood P) +
          v • ((7 : ℤ) • redGood P) := by
            rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by
        rw [hpow, hseven]
        change u • (0 : MazurProof.N18RouteC.Reduction.RedPoint) +
          v • (0 : MazurProof.N18RouteC.Reduction.RedPoint) = 0
        rw [zsmul_zero, zsmul_zero, zero_add]
  exact (redGood_ker P).mp (AddMonoidHom.mem_ker.mpr hred)

theorem inFormalKernel_iff_packageII (P : GoodPoint) :
    InFormalKernel P ↔ MazurProof.N18PackageII.InFormalKernel P := by
  cases P with
  | zero => exact iff_of_true (Or.inl rfl) trivial
  | some x y h =>
      simp [InFormalKernel, xCoordGood, MazurProof.N18PackageII.InFormalKernel]

/-- Package II, restated in the exact form consumed by `FormalKernel18`:
a nonzero torsion point in the first formal-kernel step has order exactly one.
The contradiction at order at least two is exactly
`N18PackageII.msq_torsionFree`. -/
theorem torsion_val_eq_one_good (P : GoodPoint)
    (hP : InFormalKernel P)
    (hz : MazurProof.N18PackageII.zParamGood P ≠ 0)
    (htor : ∃ n : ℕ, 0 < n ∧ n • P = 0) :
    vpiGood (MazurProof.N18PackageII.zParamGood P) = 1 := by
  have hPkg : MazurProof.N18PackageII.InFormalKernel P :=
    (inFormalKernel_iff_packageII P).mp hP
  have hpos : 0 < ordPi (MazurProof.N18PackageII.zParamGood P) := by
    rcases hP with hzero | hx
    · subst P
      exact (hz rfl).elim
    · have hv := vpi_pos_bridge_good P hx
      rw [vpiGood_apply_of_ne hz] at hv
      exact_mod_cast hv
  have hord : ordPi (MazurProof.N18PackageII.zParamGood P) = 1 := by
    by_contra hne
    have hlevel : 2 ≤ ordPi (MazurProof.N18PackageII.zParamGood P) := by
      omega
    exact MazurProof.N18PackageII.msq_torsionFree hPkg hlevel htor
  rw [vpiGood_apply_of_ne hz, hord]
  norm_num

/-! ## Good-model `FormalKernelData` and the abstract Block-5 instance -/

/-- The concrete interface carried by the good model. -/
structure FormalKernelData where
  zParam : GoodPoint → L
  vpi : AddValuation L (WithTop ℤ)
  vpi_three : vpi (3 : L) = (3 : WithTop ℤ)
  vpi_unit : ∀ m : ℤ, ¬ (3 ∣ m) → vpi (m : L) = 0
  zParam_zero : zParam 0 = 0
  vpi_zParam_neg : ∀ P, InFormalKernel P →
    vpi (zParam (-P)) = vpi (zParam P)
  zParam_eq_zero : ∀ P, InFormalKernel P → zParam P = 0 → P = 0
  add_congr : ∀ P Q, InFormalKernel P → InFormalKernel Q →
    2 * min (vpi (zParam P)) (vpi (zParam Q)) ≤
      vpi (zParam (P + Q) - zParam P - zParam Q)
  vpi_pos_bridge : ∀ P, ordPi (xCoordGood P) < 0 → 0 < vpi (zParam P)
  kernel_add_closed : ∀ P Q, InFormalKernel P → InFormalKernel Q →
    InFormalKernel (P + Q)
  msq_torsionFree : ∀ P, InFormalKernel P → zParam P ≠ 0 →
    (∃ n : ℕ, 0 < n ∧ n • P = 0) → vpi (zParam P) = 1
  three_pow_torsion_mem_kernel : ∀ P,
    (∃ k : ℕ, ((3 : ℤ) ^ k) • P = 0) → InFormalKernel P

/-- Faithfulness of `z = -x/y` on the good formal kernel. -/
theorem zParamGood_eq_zero_good (P : GoodPoint)
    (hP : InFormalKernel P)
    (hz : MazurProof.N18PackageII.zParamGood P = 0) : P = 0 := by
  rcases hP with hzero | hx
  · exact hzero
  · cases P with
    | zero => rfl
    | some x y h =>
        simp only [xCoordGood] at hx
        have hx0 : x ≠ 0 := by
          intro hzero
          rw [hzero, ordPi_zero] at hx
          omega
        have hy0 : y ≠ 0 := yCoordGood_ne_zero_of_ordPi_x_neg h hx
        exfalso
        exact (div_ne_zero (neg_ne_zero.mpr hx0) hy0)
          (by simpa using hz)

/-- Package I + Package II + the explicit good-model coordinate bridges. -/
noncomputable def goodFormalKernelData : FormalKernelData where
  zParam := MazurProof.N18PackageII.zParamGood
  vpi := vpiGood
  vpi_three := vpiGood_three
  vpi_unit := vpiGood_unit
  zParam_zero := MazurProof.N18PackageII.zParamGood_zero
  vpi_zParam_neg := vpi_zParamGood_neg
  zParam_eq_zero := zParamGood_eq_zero_good
  add_congr := add_congr_good_weak
  vpi_pos_bridge := vpi_pos_bridge_good
  kernel_add_closed := kernel_add_closed_good
  msq_torsionFree := torsion_val_eq_one_good
  three_pow_torsion_mem_kernel := three_pow_torsion_mem_kernel_good

namespace FormalKernelData

variable (D : FormalKernelData)

/-- The formal kernel as an additive subgroup of `E0Good(L)`. -/
def kernelSubgroup : AddSubgroup GoodPoint where
  carrier := {P | InFormalKernel P}
  zero_mem' := zero_mem_formalKernel
  add_mem' := by
    intro P Q hP hQ
    exact D.kernel_add_closed P Q hP hQ
  neg_mem' := by
    intro P hP
    rcases hP with hzero | hx
    · subst P
      exact Or.inl rfl
    · exact Or.inr (by rw [xCoordGood_neg]; exact hx)

theorem mem_kernelSubgroup {P : GoodPoint} :
    P ∈ D.kernelSubgroup ↔ InFormalKernel P := Iff.rfl

theorem vpi_pos_of_mem {P : GoodPoint} (hP : P ∈ D.kernelSubgroup) :
    0 < D.vpi (D.zParam P) := by
  rcases hP with hzero | hx
  · rw [hzero, D.zParam_zero, AddValuation.map_zero]
    simpa using WithTop.coe_lt_top (0 : ℤ)
  · exact D.vpi_pos_bridge P hx

theorem zero_le_vpi_natCast (k : ℕ) :
    (0 : WithTop ℤ) ≤ D.vpi (k : L) := by
  induction k with
  | zero => rw [Nat.cast_zero, D.vpi.map_zero]; exact le_top
  | succ n ih =>
      rw [Nat.cast_succ]
      exact D.vpi.map_le_add ih (le_of_eq D.vpi.map_one.symm)

/-- Package I gives the uniform weak scalar congruence. -/
theorem zParam_nsmul_congr (P : GoodPoint) (hmem : P ∈ D.kernelSubgroup) :
    ∀ n : ℕ, 1 ≤ n →
      2 • D.vpi (D.zParam P) ≤
          D.vpi (D.zParam (n • P) - n • D.zParam P) ∧
      D.vpi (D.zParam P) ≤ D.vpi (D.zParam (n • P)) := by
  have hpos : 0 < D.vpi (D.zParam P) := D.vpi_pos_of_mem hmem
  intro n
  induction n with
  | zero => intro h; exact absurd h (by norm_num)
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine ⟨?_, ?_⟩
        · rw [zero_add, one_nsmul, one_nsmul, sub_self, D.vpi.map_zero]
          exact le_top
        · rw [zero_add, one_nsmul]
      · obtain ⟨ih1, ih2⟩ := ih hk
        have hB1 : 2 • D.vpi (D.zParam P) ≤
            D.vpi (D.zParam (k • P + P) - D.zParam (k • P) - D.zParam P) := by
          have hmin :
              min (D.vpi (D.zParam (k • P))) (D.vpi (D.zParam P)) =
                D.vpi (D.zParam P) := min_eq_right ih2
          calc
            2 • D.vpi (D.zParam P) =
                2 * min (D.vpi (D.zParam (k • P)))
                  (D.vpi (D.zParam P)) := by
                    rw [hmin]
                    exact two_nsmul_eq_two_mul _
            _ ≤ D.vpi
                (D.zParam (k • P + P) - D.zParam (k • P) - D.zParam P) :=
              D.add_congr (k • P) P
                ((D.mem_kernelSubgroup).mp (nsmul_mem hmem k))
                ((D.mem_kernelSubgroup).mp hmem)
        have key :
            D.zParam ((k + 1) • P) - (k + 1) • D.zParam P =
              (D.zParam (k • P + P) - D.zParam (k • P) - D.zParam P) +
                (D.zParam (k • P) - k • D.zParam P) := by
          rw [succ_nsmul P k, succ_nsmul (D.zParam P) k]
          abel
        have hclaim1 : 2 • D.vpi (D.zParam P) ≤
            D.vpi (D.zParam ((k + 1) • P) - (k + 1) • D.zParam P) := by
          rw [key]
          exact D.vpi.map_le_add hB1 ih1
        refine ⟨hclaim1, ?_⟩
        have hval_smul : D.vpi (D.zParam P) ≤
            D.vpi ((k + 1) • D.zParam P) := by
          rw [nsmul_eq_mul, D.vpi.map_mul]
          exact le_add_of_nonneg_left (D.zero_le_vpi_natCast (k + 1))
        have ha_le : D.vpi (D.zParam P) ≤ 2 • D.vpi (D.zParam P) := by
          rw [two_nsmul]
          exact le_add_of_nonneg_left (le_of_lt hpos)
        have hdecomp : D.zParam ((k + 1) • P) =
            (D.zParam ((k + 1) • P) - (k + 1) • D.zParam P) +
              (k + 1) • D.zParam P := by
          abel
        rw [hdecomp]
        exact D.vpi.map_le_add (le_trans ha_le hclaim1) hval_smul

theorem vpi_zParam_nsmul (P : GoodPoint) (hmem : P ∈ D.kernelSubgroup)
    (n : ℕ) (hn : ¬ (3 ∣ (n : ℤ))) :
    D.vpi (D.zParam (n • P)) = D.vpi (D.zParam P) := by
  have hpos : 0 < D.vpi (D.zParam P) := D.vpi_pos_of_mem hmem
  rcases eq_or_ne (D.zParam P) 0 with hzero | hz
  · have hP0 : P = 0 := D.zParam_eq_zero P
      ((D.mem_kernelSubgroup).mp hmem) hzero
    subst P
    rw [nsmul_zero_good]
  · have hfinite : D.vpi (D.zParam P) ≠ ⊤ := by
      rw [D.vpi.ne_top_iff]
      exact hz
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · exact absurd (by norm_num) hn
      · exact hnpos
    obtain ⟨hcongr, _⟩ := D.zParam_nsmul_congr P hmem n hn1
    have hunit : D.vpi (n : L) = 0 := by
      simpa using D.vpi_unit (n : ℤ) hn
    have hlinear : D.vpi (n • D.zParam P) = D.vpi (D.zParam P) := by
      rw [nsmul_eq_mul, D.vpi.map_mul, hunit, zero_add]
    have hlt : D.vpi (n • D.zParam P) <
        D.vpi (D.zParam (n • P) - n • D.zParam P) := by
      rw [hlinear]
      exact lt_of_lt_of_le
        (MazurProof.N18Block5Instantiation.lt_two_nsmul hpos hfinite) hcongr
    have hdecomp : D.zParam (n • P) =
        n • D.zParam P + (D.zParam (n • P) - n • D.zParam P) := by
      abel
    rw [hdecomp, D.vpi.map_add_eq_of_lt_left hlt, hlinear]

theorem vpi_zParam_zsmul (P : GoodPoint) (hmem : P ∈ D.kernelSubgroup)
    (m : ℤ) (hm : ¬ (3 ∣ m)) :
    D.vpi (D.zParam (m • P)) = D.vpi (D.zParam P) := by
  cases m with
  | ofNat n =>
    change D.vpi (D.zParam (n • P)) = D.vpi (D.zParam P)
    exact D.vpi_zParam_nsmul P hmem n hm
  | negSucc n =>
    change D.vpi (D.zParam (-((n + 1) • P))) = D.vpi (D.zParam P)
    rw [D.vpi_zParam_neg _
      ((D.mem_kernelSubgroup).mp (nsmul_mem hmem (n + 1)))]
    apply D.vpi_zParam_nsmul P hmem
    intro hd
    apply hm
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
    exact dvd_neg.mpr hd

/-- The abstract Block-5 formal-kernel object on the good model. -/
def formalKernel18 : _root_.FormalKernel18 where
  M := D.kernelSubgroup
  addCommGroup := inferInstance
  val := fun z ↦ MazurProof.N18Block5Instantiation.toENat
    (D.vpi (D.zParam (z : GoodPoint)))
  val_eq_top := by
    intro z
    rw [MazurProof.N18Block5Instantiation.toENat_eq_top, D.vpi.top_iff]
    constructor
    · intro h
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero]
      exact D.zParam_eq_zero _ z.property h
    · intro h
      have hz : (z : GoodPoint) = 0 := by rw [h, ZeroMemClass.coe_zero]
      rw [hz, D.zParam_zero]
  one_le_val := by
    intro z _
    exact MazurProof.N18Block5Instantiation.one_le_toENat_of_pos
      (D.vpi_pos_of_mem z.property)
  val_unit_smul := by
    intro m hm z
    have hcoe : ((m • z : D.kernelSubgroup) : GoodPoint) =
        m • (z : GoodPoint) := by
      rw [AddSubgroupClass.coe_zsmul]
    rw [hcoe]
    exact congrArg MazurProof.N18Block5Instantiation.toENat
      (D.vpi_zParam_zsmul _ z.property m hm)
  val_three_smul_ge := by
    intro z
    have hpos : 0 < D.vpi (D.zParam (z : GoodPoint)) :=
      D.vpi_pos_of_mem z.property
    have hcoe : (((3 : ℤ) • z : D.kernelSubgroup) : GoodPoint) =
        (3 : ℕ) • (z : GoodPoint) := by
      rw [AddSubgroupClass.coe_zsmul,
        show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_cast, natCast_zsmul]
    rw [hcoe]
    obtain ⟨hcongr, _⟩ := D.zParam_nsmul_congr
      (z : GoodPoint) z.property 3 (by norm_num)
    have hthree : D.vpi ((3 : ℕ) • D.zParam (z : GoodPoint)) =
        3 + D.vpi (D.zParam (z : GoodPoint)) := by
      rw [nsmul_eq_mul, D.vpi.map_mul]
      congr 1
      rw [show ((3 : ℕ) : L) = (3 : L) by norm_cast]
      exact D.vpi_three
    have hdecomp : D.zParam ((3 : ℕ) • (z : GoodPoint)) =
        (3 : ℕ) • D.zParam (z : GoodPoint) +
          (D.zParam ((3 : ℕ) • (z : GoodPoint)) -
            (3 : ℕ) • D.zParam (z : GoodPoint)) := by
      abel
    have hbound :
        min (3 + D.vpi (D.zParam (z : GoodPoint)))
            (2 • D.vpi (D.zParam (z : GoodPoint))) ≤
          D.vpi (D.zParam ((3 : ℕ) • (z : GoodPoint))) := by
      rw [hdecomp]
      exact le_trans (min_le_min (le_of_eq hthree.symm) hcongr)
        (D.vpi.map_add _ _)
    have hbridge :
        MazurProof.N18Block5Instantiation.toENat
            (min (3 + D.vpi (D.zParam (z : GoodPoint)))
              (2 • D.vpi (D.zParam (z : GoodPoint)))) =
          min
            (3 + MazurProof.N18Block5Instantiation.toENat
              (D.vpi (D.zParam (z : GoodPoint))))
            (2 * MazurProof.N18Block5Instantiation.toENat
              (D.vpi (D.zParam (z : GoodPoint)))) := by
      rw [MazurProof.N18Block5Instantiation.toENat_min,
        MazurProof.N18Block5Instantiation.toENat_three_add (le_of_lt hpos),
        MazurProof.N18Block5Instantiation.toENat_two_nsmul (le_of_lt hpos)]
    calc
      min
          (3 + MazurProof.N18Block5Instantiation.toENat
            (D.vpi (D.zParam (z : GoodPoint))))
          (2 * MazurProof.N18Block5Instantiation.toENat
            (D.vpi (D.zParam (z : GoodPoint)))) =
        MazurProof.N18Block5Instantiation.toENat
          (min (3 + D.vpi (D.zParam (z : GoodPoint)))
            (2 • D.vpi (D.zParam (z : GoodPoint)))) := hbridge.symm
      _ ≤ MazurProof.N18Block5Instantiation.toENat
          (D.vpi (D.zParam ((3 : ℕ) • (z : GoodPoint)))) :=
        MazurProof.N18Block5Instantiation.toENat_mono hbound
  torsion_val_eq_one := by
    intro z hz htor
    have hzne : D.zParam (z : GoodPoint) ≠ 0 := by
      intro h
      apply hz
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero]
      exact D.zParam_eq_zero _ z.property h
    have htor' : ∃ n : ℕ, 0 < n ∧ n • (z : GoodPoint) = 0 := by
      obtain ⟨n, hn, hnz⟩ := htor
      refine ⟨n, hn, ?_⟩
      have := congrArg Subtype.val hnz
      rwa [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero] at this
    have hv := D.msq_torsionFree (z : GoodPoint) z.property hzne htor'
    rw [hv, MazurProof.N18Block5Instantiation.toENat_one]

include D

/-- Package III plus the abstract Block-5 Lemma C. -/
theorem three_power_torsion_exponent_three
    (P : GoodPoint) (hP : ∃ k : ℕ, ((3 : ℤ) ^ k) • P = 0) :
    (3 : ℤ) • P = 0 := by
  have hmem : P ∈ D.kernelSubgroup :=
    D.three_pow_torsion_mem_kernel P hP
  let z : D.kernelSubgroup := ⟨P, hmem⟩
  obtain ⟨k, hk⟩ := hP
  have hknat : ((3 : ℕ) ^ k) • P = 0 := by
    have hcast : ((3 : ℤ) ^ k) • P =
        (((3 : ℕ) ^ k : ℕ) : ℤ) • P := by norm_cast
    rw [hcast, natCast_zsmul] at hk
    exact hk
  have hkz : ((3 : ℕ) ^ k) • z = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
    exact hknat
  have h3z := D.formalKernel18.three_power_torsion_exponent_three z k hkz
  have := congrArg Subtype.val h3z
  change (3 : ℤ) • P = 0 at this
  exact this

/-- Identify the reduction kernel with the formal-kernel subgroup. -/
def kerEquiv
    (red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint)
    (hker : ∀ P, P ∈ (red.ker : AddSubgroup GoodPoint) ↔
      P ∈ D.kernelSubgroup) :
    (red.ker : AddSubgroup GoodPoint) ≃+ D.kernelSubgroup where
  toFun P := ⟨(P : GoodPoint), (hker P).mp P.property⟩
  invFun P := ⟨(P : GoodPoint), (hker P).mpr P.property⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl
  map_add' _ _ := rfl

/-- Strict growth of the good formal parameter under multiplication by three. -/
def formalFiltration
    (red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint)
    (hker : ∀ P, P ∈ (red.ker : AddSubgroup GoodPoint) ↔
      P ∈ D.kernelSubgroup) :
    MazurProof.N18RouteC.Separated.StrictNSmulFiltration
      (red.ker : AddSubgroup GoodPoint) 3 where
  level P := (D.formalKernel18.val (D.kerEquiv red hker P)).toNat
  step := by
    intro P hP0 h3P0
    have hmap : D.kerEquiv red hker ((3 : ℕ) • P) =
        (3 : ℕ) • D.kerEquiv red hker P := map_nsmul _ _ _
    rw [hmap]
    let z := D.kerEquiv red hker P
    have hz0 : z ≠ 0 := by
      intro hz
      apply hP0
      apply (D.kerEquiv red hker).injective
      have hz' : D.kerEquiv red hker P = 0 := by simpa [z] using hz
      simpa using hz'
    have h3z0 : (3 : ℕ) • z ≠ 0 := by
      intro h3z
      apply h3P0
      apply (D.kerEquiv red hker).injective
      rw [map_zero, map_nsmul]
      exact h3z
    have hone : (1 : ℕ∞) ≤ D.formalKernel18.val z :=
      D.formalKernel18.one_le_val z hz0
    have hge := D.formalKernel18.val_three_smul_ge z
    have hstep : D.formalKernel18.val z + 1 ≤
        D.formalKernel18.val ((3 : ℕ) • z) := by
      refine le_trans ?_ hge
      apply le_min
      · calc
          D.formalKernel18.val z + 1 ≤
              D.formalKernel18.val z + 3 := add_le_add le_rfl (by norm_num)
          _ = 3 + D.formalKernel18.val z := add_comm _ _
      · calc
          D.formalKernel18.val z + 1 ≤
              D.formalKernel18.val z + D.formalKernel18.val z :=
            add_le_add le_rfl hone
          _ = 2 * D.formalKernel18.val z := (two_mul _).symm
    have hzTop : D.formalKernel18.val z ≠ ⊤ :=
      (D.formalKernel18.val_eq_top z).not.mpr hz0
    have h3zTop : D.formalKernel18.val ((3 : ℕ) • z) ≠ ⊤ :=
      (D.formalKernel18.val_eq_top _).not.mpr h3z0
    calc
      (D.formalKernel18.val z).toNat + 1 =
          (D.formalKernel18.val z + 1).toNat := by
        rw [ENat.toNat_add hzTop ENat.one_ne_top, ENat.toNat_one]
      _ ≤ (D.formalKernel18.val ((3 : ℕ) • z)).toNat :=
        ENat.toNat_le_toNat hstep h3zTop

end FormalKernelData

/-! ## Uniform annihilation, transport, and Block 7 -/

theorem redGood_ker_formalKernel (P : GoodPoint) :
    P ∈ redGood.ker ↔ P ∈ goodFormalKernelData.kernelSubgroup := by
  rw [redGood_ker]
  rfl

/-- Transport the committed weak three-descent to the integral good equation. -/
theorem weak_three_descent_good (P : GoodPoint) :
    ∃ h : GoodPoint, 3 • h = 0 ∧
      ∃ Q : GoodPoint, P = h + 3 • Q := by
  obtain ⟨h, hh, Q, hPQ⟩ :=
    MazurProof.N18RouteC.Block4.weak_three_descent
      (MazurProof.N18RouteC.GoodModel.e0GoodEquiv.symm P)
  refine ⟨MazurProof.N18RouteC.GoodModel.e0GoodEquiv h, ?_,
    MazurProof.N18RouteC.GoodModel.e0GoodEquiv Q, ?_⟩
  · simpa using congrArg MazurProof.N18RouteC.GoodModel.e0GoodEquiv hh
  · simpa using congrArg MazurProof.N18RouteC.GoodModel.e0GoodEquiv hPQ

/-- The complete Block-5 output on the good model. -/
theorem h21_good : ∀ P : GoodPoint, (21 : ℕ) • P = 0 := by
  exact MazurProof.N18RouteC.Separated.e0_killed_by_21
    (E0Point := GoodPoint) (LocalPoint := GoodPoint)
    (RedPoint := MazurProof.N18RouteC.Reduction.RedPoint)
    (AddMonoidHom.id GoodPoint)
    Function.injective_id
    redGood weak_three_descent_good
    MazurProof.N18RouteC.Reduction.seven_nsmul
    (goodFormalKernelData.formalFiltration redGood redGood_ker_formalKernel)

/-- Transport `[21]`-annihilation back to the original quotient equation. -/
theorem h21_E0 : ∀ P : E0Point, (21 : ℕ) • P = 0 := by
  intro P
  apply MazurProof.N18RouteC.GoodModel.e0GoodEquiv.injective
  simpa only [map_nsmul, map_zero] using
    h21_good (MazurProof.N18RouteC.GoodModel.e0GoodEquiv P)

/-- Reduction on the original equation, defined by transport through the good
model. -/
noncomputable def red_E0 :
    E0Point →+ MazurProof.N18RouteC.Reduction.RedPoint :=
  redGood.comp MazurProof.N18RouteC.GoodModel.e0GoodEquiv.toAddMonoidHom

/-- Reduction is injective on seven-torsion.  The proof is the abstract
prime-to-three formal-kernel lemma applied after transport to `E0Good`. -/
theorem hker7 (P : E0Point)
    (h7 : (7 : ℕ) • P = 0) (hred : red_E0 P = 0) : P = 0 := by
  let PG : GoodPoint := MazurProof.N18RouteC.GoodModel.e0GoodEquiv P
  have hredG : redGood PG = 0 := by
    simpa [red_E0, PG] using hred
  have hmemRed : PG ∈ redGood.ker := AddMonoidHom.mem_ker.mpr hredG
  have hmem : PG ∈ goodFormalKernelData.kernelSubgroup :=
    (redGood_ker_formalKernel PG).mp hmemRed
  let z : goodFormalKernelData.kernelSubgroup := ⟨PG, hmem⟩
  have h7PG : (7 : ℕ) • PG = 0 := by
    simpa [PG] using
      congrArg MazurProof.N18RouteC.GoodModel.e0GoodEquiv h7
  have h7z : (7 : ℤ) • z = 0 := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_zsmul, ZeroMemClass.coe_zero,
      show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_cast, natCast_zsmul]
    exact h7PG
  have hz0 : z = 0 :=
    goodFormalKernelData.formalKernel18.no_prime_to_3_torsion
      7 (by norm_num) z h7z
  have hPG0 : PG = 0 := by
    simpa [z] using congrArg Subtype.val hz0
  apply MazurProof.N18RouteC.GoodModel.e0GoodEquiv.injective
  simpa [PG] using hPG0

/-- The weak descent with its representative retained in the explicit
three-element subgroup `H3`, as required by Block 7. -/
theorem weak_three_descent_H3 (P : E0Point) :
    ∃ h : H3, ∃ Q : E0Point, P = (h : E0Point) + 3 • Q := by
  obtain ⟨n, c, hc⟩ :=
    MazurProof.N18RouteC.DualSurvivor.kappa_cube_after_sub_torsion P
  obtain ⟨R, hR⟩ :=
    MazurProof.N18RouteC.DualPreimage.exists_phihat_preimage_of_kappa_cube
      (P - n.val • T) ⟨c, hc⟩
  obtain ⟨Q, hQ⟩ :=
    MazurProof.N18RouteC.PhiPreimage.phiPoint_surjective R
  let h : H3 := ⟨n.val • T, nsmul_mem (AddSubgroup.mem_zmultiples T) n.val⟩
  refine ⟨h, Q, ?_⟩
  calc
    P = n.val • T + (P - n.val • T) := by abel
    _ = n.val • T + phihatPoint R := by rw [hR]
    _ = n.val • T + phihatPoint (phiPoint Q) := by rw [hQ]
    _ = (h : E0Point) + 3 • Q := by
      rw [MazurProof.N18RouteC.Composition.phihat_phi_point]

/-- Block 7 and the verified twenty-one-point fiber table. -/
theorem all_rational_points_are_cusps :
    ∀ P : CurvePointQ, CurvePoint.IsCusp P :=
  MazurProof.N18RouteC.Block7.all_rational_points_are_cusps
    h21_E0 weak_three_descent_H3 red_E0 hker7

/-! ## Closing the elementary five-descent endpoint -/

theorem curvePolynomial_neg_eq_hyperellipticF18 (U : ℚ) :
    curvePolynomial (-U) = MazurProof.RationalPointsN18.hyperellipticF18 U := by
  unfold curvePolynomial MazurProof.RationalPointsN18.hyperellipticF18
  ring

/-- The final five-descent contradiction.  The reverse bridge constructs a
noncuspidal rational point, whereas Block 7 says that every rational point is
a cusp. -/
theorem no_five_descent_solution :
    ¬ ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧ 0 < e ∧ 0 < f ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧
      Int.gcd D (A + D) = 1 ∧ Int.gcd e f = 1 ∧
      e * f = A * D * (A + D) ∧
      ((MazurProof.RationalPointsN18Descent.normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2) ∨
       (MazurProof.RationalPointsN18Descent.normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2)) ∧
      (((5 : ℤ) ∣ e ∧ ¬ (5 : ℤ) ∣ f) ∨
        ((5 : ℤ) ∣ f ∧ ¬ (5 : ℤ) ∣ e)) ∧
      (((5 : ℤ) ∣ A ∧ ¬ (5 : ℤ) ∣ D ∧ ¬ (5 : ℤ) ∣ A + D) ∨
       ((5 : ℤ) ∣ D ∧ ¬ (5 : ℤ) ∣ A ∧ ¬ (5 : ℤ) ∣ A + D) ∨
       ((5 : ℤ) ∣ A + D ∧ ¬ (5 : ℤ) ∣ A ∧ ¬ (5 : ℤ) ∣ D)) := by
  rintro ⟨A, D, C, e, f, hA, hD, _he, _hf,
    _hAD, _hAAS, _hDAS, _hefCop, hef, hforms, _hfiveEF, _hfiveAD⟩
  obtain ⟨U, Y, hU0, hU1, hY⟩ :=
    MazurProof.RationalPointsN18Descent.five_descent_to_noncuspidal
      hA hD hef hforms
  have hcurve : Y ^ 2 = curvePolynomial (-U) := by
    rw [curvePolynomial_neg_eq_hyperellipticF18]
    exact hY
  let P : CurvePointQ := .affine (-U) Y hcurve
  have hnot : ¬ CurvePoint.IsCusp P := by
    apply CurvePoint.affine_not_cusp_of_x_ne
    · exact neg_ne_zero.mpr hU0
    · intro hneg
      apply hU1
      linarith
  exact hnot (all_rational_points_are_cusps P)

end

end MazurProof.N18GoodModelAssembly
