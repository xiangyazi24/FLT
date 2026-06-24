# 14a4 forward map — COMPLETE design (Xiang-pasted dm1 Q9, authoritative)

Ignore the ZMod 2 component. R := f(0,1) has order 14. Normalize (E,R) to Tate normal form R↦(0,0),
then map to X14: s²+ts+s=t³-t. Independent 2-torsion irrelevant. Reuses variableChangePointAddEquiv (N10/N12).

## First lemma to dispatch
theorem tateOrder14Good_of_addOrderOf_origin {b c} (hord : addOrderOf (tateOrigin14 b c) = 14) : TateOrder14Good b c

## Tate curve + multiples
Tate14Curve b c := {a₁:=1-c, a₂:=-b, a₃:=-b, a₄:=0, a₆:=0}
tateX2=b, tateY2=b*c ; tateX3=c, tateY3=b-c
tateX4 = b*(b-c)/c² ; tateY4 = -b²*(b-c²-c)/c³
tateX5 = -b*c*(b-c²-c)/(b-c)² ; tateY5 = b*c²*(b²-b*c-c³)/(b-c)³
tateX6 = (b-c)*(b²-b*c-c³)/(b-c²-c)² ; tateY6 = c*(b-c)²*(2b²-b*c²-3b*c+c²)/(b-c²-c)³
tateX7 = b*c*(b-c²-c)*(2b²-b*c²-3b*c+c²)/(b²-b*c-c³)²
tateY7 = b²*(b-c²-c)²*(b³-3b²c+b*c³+3b*c²-c⁵-c⁴-c³)/(b²-b*c-c³)³

## Order-14 polynomial (7P is 2-torsion: 2y₇+(1-c)x₇-b=0):
Phi14 b c = b⁶ -6b⁵c² -5b⁵c +5b⁴c⁴ +25b⁴c³ +10b⁴c² -b³c⁶ -16b³c⁵ -40b³c⁴ -10b³c³
  +4b²c⁷ +17b²c⁶ +30b²c⁵ +5b²c⁴ -b*c⁹ -3b*c⁸ -6b*c⁷ -10b*c⁶ -b*c⁵ +c⁷

## T14/S14 Kubert map (the forward witness):
Tnum14 = b³-4b²c²-3b²c+2b*c⁴+7b*c³+3b*c²-c⁵-3c⁴-c³
Tden14 = c*(3b²c-b²-2b*c³-3b*c²+2b*c-c²)
Snum14 = -(b³-4b²c²-3b²c+7b*c³+4b*c²+2c⁵-4c⁴-2c³)
Sden14 = 4b²c²-2b²c+b²-3b*c⁴-3b*c³+2b*c²-2b*c+c²
T14=Tnum14/Tden14, S14=Snum14/Sden14, X14Equation t s := s²+t*s+s=t³-t

## TateOrder14Good structure: hb,hc,hbc,h4den,h6den (nonzero factors) + hPhi(Phi14=0)
##   + hTden,hSden ≠0 + hT_ne_zero/one/neg_one (cusp exclusions t∉{-1,0,1})

## Key certificate (proof = ring_nf + rw[hPhi]; ring): X14Equation_of_TateOrder14Good
##   field_simp[hTden,hSden]; ring_nf; numerator = -Phi14·(deg-19 cofactor); rw[hPhi]; ring.
## Nondegeneracy from the hT_ne_* exclusions. order14_of_injective_Z2xZ14 via AddMonoidHom.addOrderOf_of_injective.

## VERDICT: easier than N12 (no 2-torsion, no Ljunggren). Only seam = X14_points_degenerate
##   (= the 14a4/Q14 rank-0 enumeration, built separately in scratch/ObstructionQ14.lean).
