import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Scalar-safe local intersection lengths

The length of a finite quotient over its ground field is not automatically
its length over a point local ring.  These lemmas expose the residue-field
factor required to pass between the two scalar rings.
-/

namespace MazurProof.CurveLocalIntersectionLength

/-- A quotient module has the same length over the source ring and over the
quotient ring itself. -/
theorem length_quotient_eq_length_self
    {A : Type*} [CommRing A] (I : Ideal A) :
    Module.length A (A ⧸ I) =
      Module.length (A ⧸ I) (A ⧸ I) := by
  apply Module.length_eq_of_surjective
  simpa only [Ideal.Quotient.algebraMap_eq] using
    (Ideal.Quotient.mk_surjective (I := I))

/-- If a local algebra has residue-field extension length one, its
self-length equals its length over the ground field. -/
theorem self_length_eq_base_length_of_residue_length_one
    {k B : Type*}
    [Field k] [CommRing B]
    [Algebra k B] [IsLocalRing B]
    (hκ :
      Module.length (IsLocalRing.ResidueField k)
        (IsLocalRing.ResidueField B) = 1) :
    Module.length B B = Module.length k B := by
  have h := IsLocalRing.length_restrictScalars
    (A := k) (B := B) (M := B)
  rw [hκ, mul_one] at h
  exact h.symm

/-- A quotient of a local algebra has local-ring length equal to its
ground-field length once its residue-field extension has length one. -/
theorem local_quotient_length_eq_base_length_of_residue_length_one
    {k A : Type*}
    [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (hκ :
      Module.length (IsLocalRing.ResidueField k)
        (IsLocalRing.ResidueField (A ⧸ I)) = 1) :
    Module.length A (A ⧸ I) =
      Module.length k (A ⧸ I) := by
  calc
    Module.length A (A ⧸ I) =
        Module.length (A ⧸ I) (A ⧸ I) :=
      length_quotient_eq_length_self I
    _ = Module.length k (A ⧸ I) :=
      self_length_eq_base_length_of_residue_length_one hκ

end MazurProof.CurveLocalIntersectionLength
