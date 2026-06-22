# Keystone doubling certificate — CAS-VERIFIED, Lean-ready (2026-06-22)

Goal (EXACT, c=1): ΨSq(2m)=dupDenH(Φm,ΨSqm), Φ(2m)=dupNumH(Φm,ΨSqm).
Route (Ward pattern): prove Ψ₃-multiplied `c3·Δ = A·Adj + I·Inv + B·bRel` by linear_combination,
cancel c3=Ψ₃≠0 over universal domain, transport via map_ΨSq/map_Φ. ALL 4 certs sympy-verified exact 0.

Notation: s=Ψ₂Sq=4x³+b₂x²+2b₄x+b₆; c3=Ψ₃=3x⁴+b₂x³+3b₄x²+3b₆x+b₈;
d4=preΨ₄=2x⁶+b₂x⁵+5b₄x⁴+10b₆x³+10b₈x²+(b₂b₈−b₄b₆)x+(b₄b₈−b₆²);
ell=6x²+b₂x+b₄; eta=b₆+b₄x−2x³; rho0=9x⁴+2b₂x³+4b₄x²+3b₆x+b₈; rho1=5x⁴+b₂x³+2b₄x²+2b₆x+b₈;
bRel=b₂b₆−b₄²−4b₈; P_i=preΨ(m+i). Even: E2=s²,O2=1,E=s,O=1. Odd: E2=1,O2=s²,E=1,O=s.
Z=ΨSq(m)=P0²E; F=Φ(m)=xZ−P1·Pm1·O; L=Pm1²P2−Pm2P1²; ΨSq(2m)=s·P0²L²;
Aplus=P2P0³E2−Pm1P1³O2; Aminus=P1Pm1³O2−Pm2P0³E2; Φ(2m)=x·ΨSq(2m)−Aplus·Aminus.
Adj=Pm2P2−O2·Pm1P1+c3P0²  (=adjacent Somos, PROVEN as normEDS_adjacent_somos on ψ).
Inv=c3(P2Pm1²+P1²Pm2+E2P0³)−(d4+s²)P1P0Pm1  (=Ward InvarRel on ψ, PROVEN: c=Ψ₃,d+b⁴=preΨ₄+ψ₂⁴).

## Cofactors (VERIFIED c3·Δ = A·Adj+I·Inv+B·bRel exact 0):
EVEN-DEN: A=-4P0²P1²Pm1²·s·c3 ; I=-P0²s(P0³s²−P0P1Pm1·ell−P1²Pm2)+P0²Pm1²s·P2 ;
  B=P0³P1Pm1·s(P0³s²x²−P0P1Pm1·rho0−P1²Pm2x²−P2Pm1²x²)
EVEN-NUM: A=P0²s·c3(P0⁴s³−4P1²Pm1²x) ; I=-P0²s(P0³s²x+P0P1Pm1·eta−P1²Pm2x)+P0²Pm1²xs·P2 ;
  B=P0³P1Pm1·xs(P0³s²x²−P0P1Pm1·rho1−P1²Pm2x²−P2Pm1²x²)
ODD-DEN: A=-4P0²P1²Pm1²·s·c3 ; I=P0²s(−P0³+P0P1Pm1·ell+P1²Pm2)+P0²Pm1²s·P2 ;
  B=P0³P1Pm1·s(P0³x²−P0P1Pm1·rho0−P1²Pm2x²−P2Pm1²x²)
ODD-NUM: A=P0²c3(P0⁴−4P1²Pm1²xs) ; I=P0²s(−P0³x−P0P1Pm1·eta+P1²Pm2x)+P0²Pm1²xs·P2 ;
  B=P0³P1Pm1·xs(P0³x²−P0P1Pm1·rho1−P1²Pm2x²−P2Pm1²x²)

ChatGPT design Q325/Q329 dm1 (commits c5ec2e4bf, 6ac9d9020). NEXT: Lean-encode (linear_combination cofactors +
wire proven Adj/Inv + cancel Ψ₃ + transport) → SameP1Vec doubling (c=1) → companion diff-addition + nonzero facts.
