from pathlib import Path
r=Path(__file__).parent
base=(r/'BoundarySectionFiltrationFamilyInput.lean').read_text()
base='\n'.join(l for l in base.splitlines() if not l.startswith('#print axioms'))+'\n'
s=(r/'N25F_TotalBoundaryCost.lean').read_text()
body=s[s.index('/-- Sequentially'):s.index('end MazurProof.N25F_TotalBoundaryCost')]
for a,b in [('ProjectiveDivisor25Two','C.Divisor'),('(fullBoundaryAtomOfTag .X)','X'),('(fullBoundaryAtomOfTag .YZ)','Y'),('(fullBoundaryAtomOfTag .Z)','Z'),('fullRiemannRochSpace25Two D','fullRiemannRochSpace25Two C principal hmin D'),('fullRiemannRochSpace25Two\n','fullRiemannRochSpace25Two C principal hmin\n')]:body=body.replace(a,b)
body=body.replace('D .X a','C principal hmin X hx hzero hinj D a')
body=body.replace('finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple\n    (D', 'finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple C principal hmin Y hy hzero hinj\n    (D',1).replace(') .YZ b',') b')
body=body.replace('finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple\n    (D', 'finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple C principal hmin Z hz hzero hinj\n    (D',1).replace(') .Z c',') c')
head='''namespace MazurProof.N25F_TotalBoundaryCost
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_BoundarySectionFiltration
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (C : ClosedPointGrading) (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ, (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
 min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
variable (X Y Z : C.Atom)
def Cancels (P : C.Atom) : Prop := ∀ a b : L, ∀ (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b),
 principal (Additive.ofMul (Units.mk0 a ha)) P = principal (Additive.ofMul (Units.mk0 b hb)) P →
 principal (Additive.ofMul (Units.mk0 b hb)) P < principal (Additive.ofMul (Units.mk0 (a-b) (sub_ne_zero.mpr hab))) P
variable (hx : Cancels C principal X) (hy : Cancels C principal Y) (hz : Cancels C principal Z)
include hx hy hz hzero hinj in
'''
(r/'TotalBoundaryCostCheck.lean').write_text(base+head+body+'#print axioms finrank_le_sub_three_boundaries\nend MazurProof.N25F_TotalBoundaryCost\n')
