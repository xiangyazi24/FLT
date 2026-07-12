import FLT.Assumptions.MazurProof.N18MumfordUnit
import FLT.Assumptions.MazurProof.N18Infinity

/-!
# The concrete oriented Picard group for N18

The affine coordinate ring omits both points at infinity.  We therefore keep
the order at the chosen positive infinity before quotienting by principal
fractional ideals.  All group laws are inherited from Mathlib's quotient-group
and fractional-ideal machinery.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def Mumford.toSemi (D : Mumford K) : SemiMumford K where
  u := D.u
  v := D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := D.v_reduced
  curve_dvd := D.curve_dvd

@[simp] theorem toSemi_u (D : Mumford K) : D.toSemi.u = D.u := rfl
@[simp] theorem toSemi_v (D : Mumford K) : D.toSemi.v = D.v := rfl
@[simp] theorem toSemi_nInf (D : Mumford K) : D.toSemi.nInf = D.nInf := rfl

abbrev ConcretePic : Type u :=
  OrientedPic K (N18Infinity.positiveInfinityOrder K)

def mumfordRaw (D : Mumford K) : OrientedFrac K :=
  (mumfordIdealUnit K D.toSemi,
    Multiplicative.ofAdd ((D.nInf : ℤ) - 1))

def classOf (D : Mumford K) : ConcretePic K :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented K (N18Infinity.positiveInfinityOrder K)).range
      (mumfordRaw K D)

theorem classOf_eq_iff (D₁ D₂ : Mumford K) :
    classOf K D₁ = classOf K D₂ ↔
      ∃ α : (FunctionField K)ˣ,
        mumfordIdealUnit K D₁.toSemi *
              toPrincipalIdeal (CoordinateRing K) (FunctionField K) α =
            mumfordIdealUnit K D₂.toSemi ∧
        Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
              (N18Infinity.positiveInfinityOrder K).ordPlus α =
            Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
  change QuotientGroup.mk'
      (principalOriented K (N18Infinity.positiveInfinityOrder K)).range
        (mumfordRaw K D₁) =
      QuotientGroup.mk'
      (principalOriented K (N18Infinity.positiveInfinityOrder K)).range
        (mumfordRaw K D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
    refine ⟨α, ?_, ?_⟩
    · exact congrArg Prod.fst hmul
    · exact congrArg Prod.snd hmul
  · rintro ⟨α, hIdeal, hInf⟩
    refine ⟨principalOriented K (N18Infinity.positiveInfinityOrder K) α,
      MonoidHom.mem_range.mpr ⟨α, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

theorem zero_mumfordIdeal :
    mumfordIdeal K (zero K).u (zero K).v = ⊤ := by
  rw [zero_u, zero_v, mumfordIdeal]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp [xClass_one])

theorem mumfordIdealUnit_zero :
    mumfordIdealUnit K (zero K).toSemi = 1 := by
  apply Units.ext
  change (mumfordIdeal K 1 0 :
      FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)) = 1
  rw [show mumfordIdeal K 1 0 = ⊤ from zero_mumfordIdeal K]
  rfl

@[simp] theorem classOf_zero : classOf K (zero K) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented K (N18Infinity.positiveInfinityOrder K)).range
        (mumfordRaw K (zero K))) = 0
  have hraw : mumfordRaw K (zero K) = 1 := by
    apply Prod.ext
    · exact mumfordIdealUnit_zero K
    · simp [mumfordRaw]
  rw [hraw, map_one]
  rfl

end

end MazurProof.N18Mumford
