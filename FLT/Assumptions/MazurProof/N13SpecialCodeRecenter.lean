import FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient

/-!
Uncompiled candidate for FLT-C13-B03-PLANr1. All Lean checks: NOT RUN.
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
The iff below isolates the arithmetic endpoint; it does not establish the
missing degree-four principal-equivalence/code bridge.
-/

namespace MazurProof.N13.SpecialCodeRecenter

noncomputable section

open N13AbelFiberTwoModel N13SpecialAbelCode

variable {G : Type*} [AddGroup G]

/-- Code a selected special class relative to the selected identity class. -/
def specialCode (s : G → PicTwoSetModel) (P : G) : ZMod 19 :=
  picEquiv (s P) - picEquiv (s 0)

@[simp] theorem specialCode_zero (s : G → PicTwoSetModel) :
    specialCode s 0 = 0 := by
  simp [specialCode]

/-- A uniform translation of all selected special classes cancels on recentering. -/
theorem specialCode_translate (s : G → PicTwoSetModel) (r : Code) (P : G) :
    specialCode (fun Q => specialTranslateCode r (s Q)) P =
      specialCode s P := by
  simp [specialCode]

/-- Exact arithmetic form of the degree-four comparison that geometry must
supply. This is an equivalence of obligations, not a proof of either side. -/
theorem specialCode_add_iff (s : G → PicTwoSetModel) (P Q : G) :
    specialCode s (P + Q) = specialCode s P + specialCode s Q ↔
      picCode (s (P + Q)) + picCode (s 0) =
        picCode (s P) + picCode (s Q) := by
  simp only [specialCode, picEquiv_apply]
  constructor <;> intro h <;> linear_combination h

/-- The arithmetic bridge specialized to a family of effective degree-two
special divisors. Its right-hand side concerns degree-four sums. -/
theorem specialCode_abel_add_iff
    (d : G → N13SymmetricSquareTwo.EffectiveDivisorTwo) (P Q : G) :
    specialCode (fun R => abel (d R)) (P + Q) =
        specialCode (fun R => abel (d R)) P +
          specialCode (fun R => abel (d R)) Q ↔
      divisorCode (d (P + Q)) + divisorCode (d 0) =
        divisorCode (d P) + divisorCode (d Q) := by
  exact specialCode_add_iff (fun R => abel (d R)) P Q

end

end MazurProof.N13.SpecialCodeRecenter
