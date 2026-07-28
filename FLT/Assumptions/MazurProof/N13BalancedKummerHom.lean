import FLT.Assumptions.MazurProof.N13MumfordInfinityBalance
import FLT.Assumptions.MazurProof.N13MumfordKummerHom
import FLT.Assumptions.MazurProof.N13LowDegreeKummerHom

/-!
# Agreement of the balanced and low-degree N13 Kummer maps

The structural infinity-balancing theorem makes the original Kummer
construction from balanced Mumford representatives unconditional.  This file
proves that it is exactly the same homomorphism as the earlier construction
from low-degree semirepresentatives.

Thus later arithmetic arguments may use either a genuinely balanced
representative or the more economical low-degree representative without
changing the global fake-Kummer map.
-/

namespace MazurProof.N13BalancedKummerHom

noncomputable section

open SexticMumford

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev O : SexticMumford.InfinityOrder M :=
  N13Infinity.positiveInfinityOrder ℚ

abbrev G : Type :=
  SexticMumford.ConcretePic M O

abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget

/-- Balanced Mumford representatives exist for every oriented N13 class. -/
theorem balancedSurjective :
    Function.Surjective (classOf M O) :=
  N13MumfordInfinityBalance.classOf_surjective

/-- The original balanced-representative Kummer map, now unconditional. -/
def mumfordKummer : G →+ Target :=
  N13MumfordKummerHom.mumfordKummer balancedSurjective

/-- Regard a balanced representative as a low-degree semirepresentative. -/
def toLowRep (D : N13Mumford.Mumford ℚ) :
    N13LowDegreeKummerHom.LowRep where
  toSemi := D.toSemi
  degree_le_two := D.deg_u

@[simp] theorem lowClass_toLowRep
    (D : N13Mumford.Mumford ℚ) :
    N13LowDegreeKummerHom.lowClass (toLowRep D) =
      classOf M O D :=
  rfl

@[simp] theorem lowFakeClass_toLowRep
    (D : N13Mumford.Mumford ℚ) :
    N13LowDegreeKummerHom.lowFakeClass (toLowRep D) =
      N13MumfordKummerValue.mumfordFakeClass D := by
  have hu :
      N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford (toLowRep D)) =
        N13MumfordKummerValue.uThetaUnit D := by
    apply Units.ext
    rfl
  change
    Additive.ofMul
        (((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford (toLowRep D)) :
            N13MumfordKummerValue.Lˣ)) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      Additive.ofMul
        (((N13MumfordKummerValue.uThetaUnit D :
            N13MumfordKummerValue.Lˣ)) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L))
  rw [hu]

@[simp] theorem mumfordKummer_classOf
    (D : N13Mumford.Mumford ℚ) :
    mumfordKummer (classOf M O D) =
      N13MumfordKummerValue.mumfordFakeClass D :=
  N13MumfordKummerHom.mumfordKummer_classOf balancedSurjective D

/-- The balanced and low-degree constructions define the same homomorphism. -/
theorem mumfordKummer_eq_lowDegree :
    mumfordKummer = N13LowDegreeKummerHom.mumfordKummer := by
  apply AddMonoidHom.ext
  intro P
  let D : N13Mumford.Mumford ℚ :=
    N13MumfordKummerHom.representative balancedSurjective P
  have hD : classOf M O D = P :=
    N13MumfordKummerHom.classOf_representative balancedSurjective P
  calc
    mumfordKummer P =
        N13MumfordKummerValue.mumfordFakeClass D := by
      change
        N13MumfordKummerHom.mumfordKummer balancedSurjective P =
          N13MumfordKummerValue.mumfordFakeClass D
      rfl
    _ = N13LowDegreeKummerHom.lowFakeClass (toLowRep D) :=
      (lowFakeClass_toLowRep D).symm
    _ = N13LowDegreeKummerHom.mumfordKummer
          (N13LowDegreeKummerHom.lowClass (toLowRep D)) :=
      (N13LowDegreeKummerHom.mumfordKummer_lowClass
        (toLowRep D)).symm
    _ = N13LowDegreeKummerHom.mumfordKummer P := by
      rw [lowClass_toLowRep, hD]

end

end MazurProof.N13BalancedKummerHom
