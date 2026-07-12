import FLT.Assumptions.MazurProof.N18RouteC_Contracts
import FLT.Assumptions.MazurProof.N18RouteC_Modular
import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18OrientedPic

/-!
# Concrete type bindings for the N18 Route C contracts
-/

namespace MazurProof.N18RouteC.Concrete

open Contracts

noncomputable section

def types : Types where
  CQ := CurvePointQ
  CL := CurvePointL
  E0L := Isogeny.E0Point
  EhatL := Isogeny.Ehat0Point
  JQ := N18Mumford.ConcretePic ℚ
  JL := N18Mumford.ConcretePic L

def curveData : CurveData types where
  baseChangePoint := N18RouteC.baseChangePoint
  baseChangePoint_injective := N18RouteC.baseChangePoint_injective
  IsCusp := CurvePoint.IsCusp

theorem modularCapstone : TateProducesNoncusp types curveData := by
  intro E inst h18
  letI : E.IsElliptic := inst
  exact Modular.exactOrder18_to_noncusp E h18

end

end MazurProof.N18RouteC.Concrete
