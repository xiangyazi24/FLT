import FLT.Assumptions.MazurProof.N18OrientedPic

/-!
# Coefficient extension for balanced N18 Mumford representatives

This is the concrete injective part of the `ℚ → L` Picard base-change seam.
It does not assert the false general statement that affine class-group
extension is injective.  The later quotient compatibility theorem transports
this injectivity through canonical balanced representatives.
-/

open Polynomial

namespace MazurProof.N18Mumford

noncomputable section

universe u v

variable {K : Type u} {K' : Type v}
variable [Field K] [CharZero K] [Field K'] [CharZero K']

theorem f_map (ι : K →+* K') : (f K).map ι = f K' := by
  simp [f]

def Mumford.mapCoeffs (ι : K →+* K') (hι : Function.Injective ι)
    (D : Mumford K) : Mumford K' where
  u := D.u.map ι
  v := D.v.map ι
  nInf := D.nInf
  u_monic := D.u_monic.map ι
  deg_u := by
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact D.deg_u
  v_reduced := by
    rw [← Polynomial.map_mod ι, D.v_reduced]
  curve_dvd := by
    obtain ⟨q, hq⟩ := D.curve_dvd
    refine ⟨q.map ι, ?_⟩
    calc
      f K' - (D.v.map ι) ^ 2 = (f K - D.v ^ 2).map ι := by
        simp [f_map]
      _ = (D.u * q).map ι := by rw [hq]
      _ = D.u.map ι * q.map ι := by simp
  infinity_bound := by
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact D.infinity_bound

@[simp] theorem mapCoeffs_u
    (ι : K →+* K') (hι : Function.Injective ι) (D : Mumford K) :
    (D.mapCoeffs ι hι).u = D.u.map ι := rfl

@[simp] theorem mapCoeffs_v
    (ι : K →+* K') (hι : Function.Injective ι) (D : Mumford K) :
    (D.mapCoeffs ι hι).v = D.v.map ι := rfl

@[simp] theorem mapCoeffs_nInf
    (ι : K →+* K') (hι : Function.Injective ι) (D : Mumford K) :
    (D.mapCoeffs ι hι).nInf = D.nInf := rfl

theorem Mumford.mapCoeffs_injective
    (ι : K →+* K') (hι : Function.Injective ι) :
    Function.Injective (Mumford.mapCoeffs ι hι) := by
  intro D E hDE
  have huMap := congrArg Mumford.u hDE
  have hvMap := congrArg Mumford.v hDE
  have hn := congrArg Mumford.nInf hDE
  have hu : D.u = E.u :=
    Polynomial.map_injective ι hι (by simpa only [mapCoeffs_u] using huMap)
  have hv : D.v = E.v :=
    Polynomial.map_injective ι hι (by simpa only [mapCoeffs_v] using hvMap)
  have hn' : D.nInf = E.nInf := by
    simpa only [mapCoeffs_nInf] using hn
  cases D
  cases E
  simp_all

def mapQToL : Mumford ℚ → Mumford N18RouteC.L :=
  Mumford.mapCoeffs (algebraMap ℚ N18RouteC.L) (algebraMap ℚ N18RouteC.L).injective

theorem mapQToL_injective : Function.Injective mapQToL :=
  Mumford.mapCoeffs_injective
    (algebraMap ℚ N18RouteC.L) (algebraMap ℚ N18RouteC.L).injective

end

end MazurProof.N18Mumford
