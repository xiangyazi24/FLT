import FLT.Assumptions.MazurProof.N13KernelGraphContraction

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

Both a finite effective quadratic and the fixed C+B divisor acquire the
same +1 raw infinity twist when their graph is balanced. Keeping this
twist explicit proves the adapter's exact centered class equality.
-/

namespace MazurProof.N13KernelBasePic

noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def rawClass (r : SexticMumford.OrientedFrac Model) : GenericPic :=
  Additive.ofMul (QuotientGroup.mk'
    (SexticMumford.principalOriented Model
      (N13Infinity.positiveInfinityOrder Q₂)).range r)

theorem rawClass_mul (r s : SexticMumford.OrientedFrac Model) :
    rawClass (r * s) = rawClass r + rawClass s := by
  unfold rawClass
  rw [map_mul]
  rfl

def infinityShift : GenericPic := rawClass (1, Multiplicative.ofAdd 1)

theorem balancedGraph_class (D : Data) (E : N13Mumford.SemiMumford Q₂)
    (hd : E.u.natDegree ≤ 2) (hn : E.nInf = -1)
    (hr : genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E) :
    SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂)
      (balancedGraph E hd) = D.toGenericPic + infinityShift := by
  have hraw : SexticMumford.mumfordRaw Model (balancedGraph E hd) =
      genericRaw D.charts D.infinityOrder * (1, Multiplicative.ofAdd 1) := by
    rw [hr]
    apply Prod.ext
    · change SexticMumford.mumfordIdealUnit Model (balancedGraph E hd).toSemi =
        SexticMumford.mumfordIdealUnit Model E * 1
      rw [mul_one]
      apply Units.ext
      simp only [SexticMumford.coe_mumfordIdealUnit]
      rfl
    · change Multiplicative.ofAdd (-1 : ℤ) = Multiplicative.ofAdd (E.nInf - 1 + 1)
      rw [hn]
      rfl
  change rawClass _ = rawClass _ + rawClass _
  rw [hraw, rawClass_mul]

private abbrev basePair : N13TwoAdicAbelChartPic.DiskPair :=
  N13TwoAdicAbelChartData.basePair

theorem basePair_graphIdeal :
    SexticMumford.mumfordIdeal Model basePair.mumford.u basePair.mumford.v =
      SexticMumford.mumfordIdeal Model (X * (X + 1)) (2 * X + 1) := by
  have hu : basePair.mumford.u = X * (X + 1) := by
    simp [N13TwoAdicAbelChartPic.DiskPair.mumford_u,
      N13TwoAdicMumfordTransport.mapPoly, N13FormalAbelLinearization.uBase]
    ring
  have hv : basePair.mumford.v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph (X * (X + 1)) 0 := by
    rw [N13TwoAdicAbelChartPic.DiskPair.mumford_v,
      N13TwoAdicMumfordTransport.sexticSemi_v,
      N13TwoAdicAbelChartData.DiskPair.smoothMumford_u,
      N13TwoAdicAbelChartData.DiskPair.smoothMumford_v,
      N13TwoAdicAbelChartData.DiskPair.basePair_v, map_zero]
    congr 1
  rw [hu, hv]
  rw [← N13GoodSexticMumfordTransport.map_mumfordIdeal_reduced,
    N13GoodSexticMumfordTransport.map_mumfordIdeal]
  apply N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
  refine ⟨X - 1, ?_⟩
  simp only [N13GoodSexticMumfordTransport.completedGraph, mul_zero, zero_add,
    N13GeneralizedMumfordIntegral.hPoly]
  ring

private def cuspMumford (c : N13Mumford.Cusp13) : N13Mumford.Mumford Q₂ :=
  (SexticMumford.pointMumford (N13Mumford.model ℚ) (N13Mumford.cuspPoint c)).mapCoeffs
    N13InfinityBaseChange.ratToQ₂ N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)

private theorem cuspMumford_class (c : N13Mumford.Cusp13) :
    SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂) (cuspMumford c) =
      N13InfinityBaseChange.picMapRatToQ₂
        (N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint c)) := by
  exact (N13InfinityBaseChange.picMapRatToQ₂_classOf _).symm

theorem basePic_eq_translated_twist :
    N13RationalKernelDoublingAdapter.basePic =
      N13InfinityBaseChange.picMapRatToQ₂ baseTranslate + infinityShift := by
  let C := cuspMumford .zeroPlus
  let B := cuspMumford .negOneMinus
  have hpair : SexticMumford.mumfordIdeal Model C.u C.v *
      SexticMumford.mumfordIdeal Model B.u B.v =
        SexticMumford.mumfordIdeal Model basePair.mumford.u basePair.mumford.v := by
    rw [basePair_graphIdeal]
    have h := N13TwoChartLineTensor.pointIdeal_mul_eq_secantGraph
      (0 : Q₂) 1 (-1) (-1) (by norm_num)
    have hc : N13TwoChartLineTensor.secantV (0 : Q₂) 1 (-1) (-1) = 2 * X + 1 := by
      norm_num [N13TwoChartLineTensor.secantV]
      rw [show (Polynomial.C (2 : Q₂)) = 2 from rfl]
      ring
    rw [hc] at h
    simpa [C, B, cuspMumford, SexticMumford.mapCoeffs_u, SexticMumford.mapCoeffs_v,
      N13Mumford.cuspPoint, SexticMumford.pointMumford, SexticMumford.affinePointMumford]
      using h
  have hraw : SexticMumford.mumfordRaw Model basePair.mumford =
      (SexticMumford.mumfordRaw Model C * SexticMumford.mumfordRaw Model B) *
        (1, Multiplicative.ofAdd 1) := by
    apply Prod.ext
    · change SexticMumford.mumfordIdealUnit Model basePair.mumford.toSemi =
        (SexticMumford.mumfordIdealUnit Model C.toSemi *
          SexticMumford.mumfordIdealUnit Model B.toSemi) * 1
      rw [mul_one]
      apply Units.ext
      simp only [Units.val_mul, SexticMumford.coe_mumfordIdealUnit,
        ← FractionalIdeal.coeIdeal_mul]
      exact congrArg (fun I : Ideal R =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal)) hpair.symm
    · change Multiplicative.ofAdd (-1 : ℤ) =
        (Multiplicative.ofAdd (-1 : ℤ) * Multiplicative.ofAdd (-1 : ℤ)) *
          Multiplicative.ofAdd (1 : ℤ)
      decide
  change rawClass (SexticMumford.mumfordRaw Model basePair.mumford) = _
  rw [hraw, rawClass_mul, rawClass_mul]
  change SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂) C +
    SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂) B + infinityShift = _
  rw [cuspMumford_class, cuspMumford_class, baseTranslate, map_add]

end
end MazurProof.N13KernelBasePic
