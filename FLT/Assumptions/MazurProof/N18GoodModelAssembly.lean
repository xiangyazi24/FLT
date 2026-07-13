import FLT.Assumptions.MazurProof.N18AddCongrWired
import FLT.Assumptions.MazurProof.N18PackageII
import FLT.Assumptions.MazurProof.N18GoodModelValCoords
import FLT.Assumptions.MazurProof.N18VpiWrapper
import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18Block5Instantiation
import FLT.Assumptions.MazurProof.CyclicExclusion18
import FLT.Assumptions.MazurProof.N18RouteC_Block7

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

/-- The good integral equation has its usual reduction homomorphism, and the
kernel is exactly the near-origin locus.  Closing this theorem requires the
ring-of-integers reduction map and its compatibility with the affine group
law; it is independent of every later Block-5 and Block-7 argument. -/
theorem exists_good_reduction :
    ∃ red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint,
      ∀ P : GoodPoint, P ∈ red.ker ↔ InFormalKernel P := by
  sorry

/-- The reduction homomorphism selected from `exists_good_reduction`. -/
noncomputable def redGood :
    GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint :=
  Classical.choose exists_good_reduction

theorem redGood_ker (P : GoodPoint) :
    P ∈ redGood.ker ↔ InFormalKernel P :=
  Classical.choose_spec exists_good_reduction P

/-- Near-origin points are closed under addition, as a consequence of the
kernel description of reduction. -/
theorem kernel_add_closed_good (P Q : GoodPoint)
    (hP : InFormalKernel P) (hQ : InFormalKernel Q) :
    InFormalKernel (P + Q) := by
  apply (redGood_ker (P + Q)).mp
  exact add_mem ((redGood_ker P).mpr hP) ((redGood_ker Q).mpr hQ)

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
  sorry

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
