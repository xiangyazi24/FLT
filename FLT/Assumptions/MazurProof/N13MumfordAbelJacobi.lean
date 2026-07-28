import FLT.Assumptions.MazurProof.N13SmallMumfordRigidity

/-!
# The N13 Abel--Jacobi embedding in oriented Mumford coordinates

The chosen positive infinity is the base point.  A curve point is first sent
to its balanced Mumford representative and then to its oriented Picard class.
-/

namespace MazurProof.N13MumfordAbelJacobi

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

abbrev ConcretePic : Type u :=
  SexticMumford.ConcretePic (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K)

def abelJacobi :
    SexticMumford.CurvePoint (N13Mumford.model K) → ConcretePic K :=
  fun P => SexticMumford.classOf (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K)
    (SexticMumford.pointMumford (N13Mumford.model K) P)

theorem abelJacobi_injective
    : Function.Injective (abelJacobi K) := by
  exact N13SmallMumfordRigidity.point_class_injective K

abbrev Cusp13 := N13Mumford.Cusp13

def cuspPoint : Cusp13 →
    SexticMumford.CurvePoint (N13Mumford.model ℚ) :=
  N13Mumford.cuspPoint

def cuspAbelJacobi : Cusp13 → ConcretePic ℚ :=
  (abelJacobi ℚ).comp cuspPoint

theorem cuspAbelJacobi_injective
    : Function.Injective cuspAbelJacobi := by
  exact (abelJacobi_injective ℚ).comp N13Mumford.cuspPoint_injective

theorem cuspAbelJacobi_ne
    {c d : Cusp13} (hcd : c ≠ d) :
    cuspAbelJacobi c ≠ cuspAbelJacobi d := by
  exact fun h => hcd (cuspAbelJacobi_injective h)

end

end MazurProof.N13MumfordAbelJacobi
