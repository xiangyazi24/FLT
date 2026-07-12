import FLT.Assumptions.MazurProof.N18MumfordRigidity

/-!
# Inheriting the balanced Mumford group law from the oriented class group

No Cantor associativity proof occurs here.  Once the geometric normal-form
theorem supplies a unique balanced representative of every oriented class,
the full abelian-group structure is transported from Mathlib's quotient group.
-/

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

class NormalFormData : Prop where
  existsUnique : ∀ c : ConcretePic K,
    ∃! D : Mumford K, classOf K D = c

def normalize [NormalFormData K] (c : ConcretePic K) : Mumford K :=
  Classical.choose (NormalFormData.existsUnique c)

@[simp]
theorem classOf_normalize [NormalFormData K] (c : ConcretePic K) :
    classOf K (normalize K c) = c :=
  (Classical.choose_spec (NormalFormData.existsUnique c)).1

theorem normalize_eq_of_class [NormalFormData K]
    (c : ConcretePic K) (D : Mumford K) (hD : classOf K D = c) :
    normalize K c = D := by
  exact ((Classical.choose_spec (NormalFormData.existsUnique c)).2 D hD).symm

theorem classOf_injective [NormalFormData K] :
    Function.Injective (classOf K) := by
  intro D E hDE
  have hD : normalize K (classOf K E) = D :=
    normalize_eq_of_class K (classOf K E) D hDE
  have hE : normalize K (classOf K E) = E :=
    normalize_eq_of_class K (classOf K E) E rfl
  exact hD.symm.trans hE

def normalFormEquiv [NormalFormData K] : Mumford K ≃ ConcretePic K where
  toFun := classOf K
  invFun := normalize K
  left_inv D := by
    exact normalize_eq_of_class K (classOf K D) D rfl
  right_inv := classOf_normalize K

/-- The group law is inherited from `ConcretePic`; no formula-level
associativity obligation remains. -/
noncomputable instance instAddCommGroupMumford [NormalFormData K] :
    AddCommGroup (Mumford K) :=
  Equiv.addCommGroup (normalFormEquiv K)

def classEquiv [NormalFormData K] : Mumford K ≃+ ConcretePic K :=
  Equiv.addEquiv (normalFormEquiv K)

@[simp]
theorem classEquiv_apply [NormalFormData K] (D : Mumford K) :
    classEquiv K D = classOf K D := by
  rfl

@[simp]
theorem classOf_add [NormalFormData K] (D E : Mumford K) :
    classOf K (D + E) = classOf K D + classOf K E := by
  simpa only [classEquiv_apply] using (classEquiv K).map_add D E

@[simp]
theorem classOf_neg [NormalFormData K] (D : Mumford K) :
    classOf K (-D) = -classOf K D := by
  simpa only [classEquiv_apply] using (classEquiv K).map_neg D

@[simp]
theorem classOf_nsmul [NormalFormData K] (n : ℕ) (D : Mumford K) :
    classOf K (n • D) = n • classOf K D := by
  simpa only [classEquiv_apply] using map_nsmul (classEquiv K) n D

theorem group_zero_eq_balanced_zero [NormalFormData K] :
    (0 : Mumford K) = zero K := by
  apply classOf_injective K
  calc
    classOf K 0 = classEquiv K 0 := (classEquiv_apply K 0).symm
    _ = 0 := map_zero (classEquiv K)
    _ = classOf K (zero K) := (classOf_zero K).symm

end

end MazurProof.N18Mumford
