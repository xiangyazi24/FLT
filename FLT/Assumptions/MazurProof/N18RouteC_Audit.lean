import FLT.Assumptions.MazurProof.N18ConjCube
import FLT.Assumptions.MazurProof.N18MumfordAbelJacobi
import FLT.Assumptions.MazurProof.N18RouteC_BaseChange
import FLT.Assumptions.MazurProof.N18RouteC_Concrete
import FLT.Assumptions.MazurProof.N18RouteC_Descent
import FLT.Assumptions.MazurProof.N18RouteC_Fibers
import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18RouteC_Quotients
import FLT.Assumptions.MazurProof.N18RouteC_Reduction
import FLT.Assumptions.MazurProof.N18RouteC_ThreeDescent

/-!
# Compile-time audit surface for N18 Route C

This module imports every independent concrete block and exposes the exact
closed certificates at one compilation boundary.  It deliberately does not
manufacture the still-missing geometric and local-arithmetic certificates.
-/

namespace MazurProof.N18RouteC.Audit

#check N18RouteC.sigma_preserves_homogeneous
#check N18RouteC.Quotients.sigmaOpen_involutive
#check N18RouteC.Quotients.qPlus_projective_identity
#check N18RouteC.Quotients.qMinus_projective_identity

#check N18Mumford.mumfordIdealUnit
#check N18Mumford.classOf
#check N18Mumford.normalFormEquiv
#check N18Mumford.abelJacobi_injective

#check Isogeny.addOrderOf_T
#check Isogeny.card_H3
#check Isogeny.phi_preserves_curve
#check Isogeny.phihat_preserves_curve

#check ThreeDescent.candidate_count
#check ThreeDescent.local_image_cardinalities
#check ThreeDescent.weakThreeDescent

#check Reduction.redPoint_card
#check Reduction.seven_nsmul
#check Separated.e0_killed_by_21
#check Separated.pushPull_annihilator

#check Concrete.modularCapstone
#check Contracts.assemble_no_order_18

#print axioms N18RouteC.sigma_preserves_homogeneous
#print axioms N18Mumford.mumfordIdealUnit
#print axioms Isogeny.card_H3
#print axioms ThreeDescent.weakThreeDescent
#print axioms Separated.e0_killed_by_21
#print axioms Concrete.modularCapstone

end MazurProof.N18RouteC.Audit
