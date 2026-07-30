/-!
# Specialization through vertical twists

This representation-independent interface separates the divisor geometry
from its sole downstream consequence: two integral lines with the same
generic class have the same special class.
-/

namespace MazurProof.ProperLineSpecializationCore

/-- The minimal interface needed to make specialization independent of an
integral spread. -/
structure API (Line GenericGroup SpecialGroup : Type) where
  Iso : Line → Line → Prop
  genericClass : Line → GenericGroup
  specialClass : Line → SpecialGroup
  verticalTwist : Int → Line → Line

  vertical_of_generic_eq :
    ∀ {L M : Line},
      genericClass L = genericClass M →
      ∃ n : Int, Iso L (verticalTwist n M)

  special_congr :
    ∀ {L M : Line},
      Iso L M → specialClass L = specialClass M

  special_verticalTwist :
    ∀ n : Int, ∀ L : Line,
      specialClass (verticalTwist n L) = specialClass L

namespace API

variable {Line GenericGroup SpecialGroup : Type}
variable (D : API Line GenericGroup SpecialGroup)

/-- The special class depends only on the generic class. -/
theorem special_eq_of_generic_eq
    {L M : Line}
    (h : D.genericClass L = D.genericClass M) :
    D.specialClass L = D.specialClass M := by
  obtain ⟨n, hLM⟩ := D.vertical_of_generic_eq h
  calc
    D.specialClass L =
        D.specialClass (D.verticalTwist n M) :=
      D.special_congr hLM
    _ = D.specialClass M :=
      D.special_verticalTwist n M

end API

end MazurProof.ProperLineSpecializationCore
