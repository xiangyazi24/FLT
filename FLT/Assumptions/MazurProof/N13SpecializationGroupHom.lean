import FLT.Assumptions.MazurProof.N13SmallMumfordRigidity
import FLT.Assumptions.MazurProof.N13InfinityBaseChange

/-!
# Specialization group homomorphism for N13

This file constructs the specialization map

  `specialize : G →+ J₂`

as a group homomorphism from the generic Picard group (over ℚ₂) to the
special-fiber Picard group (over 𝔽₂), both equipped with the Mumford
group law from `NormalFormData`.

## Mathematical content

The key theorem is that the Néron model specialization on J₁(13) is
a group homomorphism with pro-2 kernel. Since J₁(13)(ℚ) has order 19
(prime to 2), the specialization is injective.

## What this file provides (once complete)

1. `J₂ := ConcretePic (model (ZMod 2)) O` with its AddCommGroup structure
2. `specialize : G →+ J₂` — the specialization group homomorphism
3. `AbelFiberData J₂` — J₂ has the right 19-element fiber structure
4. `FormalKernelData specialize.ker` — the kernel has pro-2 structure
5. `specialize_injective` — injectivity from items 1-4

## Current status

This file sets up the types and states the key theorems. The proofs
require connecting the ideal-level reduction to the Mumford group law.
-/

namespace MazurProof.N13SpecializationGroupHom

noncomputable section

/-- The generic Picard group, with AddCommGroup from NormalFormData. -/
abbrev G : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model N13InfinityBaseChange.Q₂)
    (N13Infinity.positiveInfinityOrder N13InfinityBaseChange.Q₂)

/-- The special-fiber Picard group over 𝔽₂, with AddCommGroup from
NormalFormData. Since `N13SmallMumfordRigidity.instNormalFormData` works
for any field K, instantiating at `K = ZMod 2` gives the group structure
on the 19-element Jacobian of the special fiber. -/
abbrev J₂ : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model (ZMod 2))
    (N13Infinity.positiveInfinityOrder (ZMod 2))

/-- J₂ has an AddCommGroup structure, inherited from NormalFormData. -/
instance : AddCommGroup J₂ := inferInstance

/-- The Mumford balanced normal form of a special-fiber Picard class. -/
def specialNormalize (c : J₂) :
    SexticMumford.Mumford (N13Mumford.model (ZMod 2)) :=
  SexticMumford.normalize
    (N13Mumford.model (ZMod 2))
    (N13Infinity.positiveInfinityOrder (ZMod 2))
    c

/-- The generic normalized Mumford datum for a rational Picard class. -/
def genericNormalize (g : G) :
    SexticMumford.Mumford (N13Mumford.model N13InfinityBaseChange.Q₂) :=
  SexticMumford.normalize
    (N13Mumford.model N13InfinityBaseChange.Q₂)
    (N13Infinity.positiveInfinityOrder N13InfinityBaseChange.Q₂)
    g

end

end MazurProof.N13SpecializationGroupHom
