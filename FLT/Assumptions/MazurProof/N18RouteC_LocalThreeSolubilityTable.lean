import FLT.Assumptions.MazurProof.N18RouteC_LocalThree

/-! Executable certificates used by the homogeneous `pi^5` solubility proof. -/

namespace MazurProof.N18RouteC.LocalThree

def OnHomogeneous (U D W : R5) : Prop :=
  W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3

def InDualLine (W : R5) : Prop :=
  ∃ m : F3, CubeEq5 W (pow two5 m.val)

instance (U D W : R5) : Decidable (OnHomogeneous U D W) := by
  unfold OnHomogeneous
  infer_instance

instance (W : R5) : Decidable (InDualLine W) := by
  unfold InDualLine
  exact Fintype.decidableExistsFintype

theorem one_isUnit5 : IsUnit5 (1 : R5) := by native_decide

theorem exists_right_inverse5 :
    ∀ x : R5, IsUnit5 x → ∃ y : R5, x * y = 1 := by
  native_decide +revert

theorem isUnit5_of_mul_eq_one :
    ∀ x y : R5, x * y = 1 → IsUnit5 y := by
  native_decide +revert

theorem isUnit5_mul {x y : R5}
    (hx : IsUnit5 x) (hy : IsUnit5 y) : IsUnit5 (x * y) := by
  revert x y
  native_decide

theorem homogeneous_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, OnHomogeneous U 1 W) → InDualLine W := by
  native_decide +revert

theorem homogeneous_nonunit_d_rep_coordinates :
    ∀ i j k : F3, ∀ U D : R5,
      IsUnit5 U → ¬IsUnit5 D →
      OnHomogeneous U D (unitRep i j k) → i = 0 ∧ j = 0 := by
  native_decide +revert

def OnScaledOne (U D W : R5) : Prop :=
  W * (pi5 ^ 3 * W - 3 * pi5 * U * D + 2 * D ^ 3) = U ^ 3

instance (U D W : R5) : Decidable (OnScaledOne U D W) := by
  unfold OnScaledOne
  infer_instance

theorem scaled_one_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, IsUnit5 U ∧ OnScaledOne U 1 W) → InDualLine W := by
  native_decide +revert

end MazurProof.N18RouteC.LocalThree
