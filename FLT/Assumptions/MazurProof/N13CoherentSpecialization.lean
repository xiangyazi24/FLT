import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence

namespace MazurProof.N13CoherentSpecialization

noncomputable section

abbrev G : Type :=
  N13RationalPointEndgame.G

abbrev SpecialSet : Type :=
  N13RationalPointEndgame.SpecialSet

/-- The special class of the fixed coherent exact normalized spread
attached to a rational Picard class. -/
def exactSpecialClass (P : G) : SpecialSet :=
  N13RationalCurvePointPicardRealization.specialClass
    (N13RationalPicardSpreadExistence.exactSpreadLine P)

end

end MazurProof.N13CoherentSpecialization
