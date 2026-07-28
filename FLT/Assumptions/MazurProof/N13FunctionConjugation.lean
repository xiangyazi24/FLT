import FLT.Assumptions.MazurProof.N13BranchNorm
import FLT.Assumptions.MazurProof.SexticFunctionConjugation

/-!
# Conjugation exchanges the two infinities of `X₁(13)`

The negative Laurent embedding is obtained from the positive embedding by the
hyperelliptic involution.  Consequently the negative order of a function is
the positive order of its conjugate.  This connects the two-branch local
calculation to the fractional-ideal Picard model.
-/

open scoped LaurentSeries

namespace MazurProof.N13FunctionConjugation

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem coordinateToLaurent_conjugate
    (z : N13Mumford.CoordinateRing K) :
    N13Infinity.coordinateToLaurent K
        (SexticMumford.conjugate (N13Mumford.model K) z) =
      N13InfinityMinus.coordinateToLaurentMinus K z := by
  conv_lhs =>
    rw [← SexticMumford.recompose (N13Mumford.model K) z]
  conv_rhs =>
    rw [← SexticMumford.recompose (N13Mumford.model K) z]
  simp only [map_add, map_mul, map_neg, SexticMumford.conjugate_xClass,
    SexticMumford.conjugate_yClass,
    N13Infinity.coordinateToLaurent_xClass,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.ySeriesMinus_eq_neg]

theorem functionFieldToLaurent_conjugate
    (z : N13Mumford.FunctionField K) :
    N13Infinity.functionFieldToLaurent K
        (SexticMumford.functionConjugateEquiv
          (N13Mumford.model K) z) =
      N13InfinityMinus.functionFieldToLaurentMinus K z := by
  let lhs : N13Mumford.FunctionField K →+* LaurentSeries K :=
    (N13Infinity.functionFieldToLaurent K).comp
      (SexticMumford.functionConjugateEquiv
        (N13Mumford.model K)).toRingHom
  have hhom :
      lhs = N13InfinityMinus.functionFieldToLaurentMinus K := by
    apply IsFractionRing.ringHom_ext
      (A := N13Mumford.CoordinateRing K)
    intro w
    change N13Infinity.functionFieldToLaurent K
        (SexticMumford.functionConjugateEquiv
          (N13Mumford.model K)
          (algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) w)) =
      N13InfinityMinus.functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) w)
    rw [SexticMumford.functionConjugateEquiv_algebraMap,
      N13Infinity.functionFieldToLaurent_algebraMap,
      N13InfinityMinus.functionFieldToLaurentMinus_algebraMap,
      coordinateToLaurent_conjugate]
  change lhs z = _
  rw [hhom]

theorem positive_order_conjugate_eq_negative
    (z : (N13Mumford.FunctionField K)ˣ) :
    (N13Infinity.positiveInfinityOrder K).ordPlus
        (SexticMumford.conjugateFunctionUnit
          (N13Mumford.model K) z) =
      (N13InfinityMinus.negativeInfinityOrder K).ordPlus z := by
  change Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent K
        (SexticMumford.functionConjugateEquiv
          (N13Mumford.model K)
          (z : N13Mumford.FunctionField K))).order) =
    Multiplicative.ofAdd
      ((N13InfinityMinus.functionFieldToLaurentMinus K
        (z : N13Mumford.FunctionField K)).order)
  rw [functionFieldToLaurent_conjugate]

end

end MazurProof.N13FunctionConjugation
