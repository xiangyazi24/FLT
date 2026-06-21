# A6-height R3: Northcott(xHeight) — COMPLETE design (Xiang-pasted real R3, authoritative)

## ELLIPTIC PART = EASY (right API already exists):
xProj P := Projectivization.mk ℚ P.xRep (xRep_ne_zero P)  -- projective [x:1], 0↦[1:0]
xHeight P := Projectivization.logHeight (xProj P)  -- USE projective, NOT raw xRep tuple
  (tuple height on Fin 2→ℚ is NOT Northcott — scale-invariant → ∞ many same-height; projective is right).

## The reduction (complete):
1. xProj_eq_xProj_iff_xRep_eq_xRep (small normalization, via Projectivization.mk_eq_mk_iff' + xRep_zero/some)
2. xProj_finite_fiber: fibers ≤2 points (via Affine.Point.xRep_eq_xRep_iff: P.xRep=Q.xRep ↔ P=Q∨P=-Q)
3. xProj_tendstoCofinite instance (tendstoCofinite_iff_finite_preimage_singleton + finite fibers)
4. xHeight_northcott_of_P1 [Northcott(Projectivization.logHeight ℚ (Fin 2))] : Northcott xHeight
   := Northcott.comp_of_finite_fibers (xProj) (Projectivization.logHeight)   ← THE core, complete.

## THE ONLY MISSING BASE THEOREM (Mathlib marks projective Northcott TODO):
rat_P1_logHeight_northcott : Northcott (Projectivization.logHeight (ℚ) (Fin 2))
  FEASIBLE: identify ℙ¹(ℚ) ≃ Option ℚ (none↦[1:0], some q↦[q:1]); ∞ pt finite; affine chart =
  Height.logHeight₁; Rat.logHeight₁_eq_log_max (= log max(num.natAbs, den)); bounded → finitely many (num,den).
  Modular: rat_logHeight₁_northcott (finite num/den) + ℙ¹≃Option ℚ chart.

## VERDICT: elliptic part complete with existing API; only base ℙ¹(ℚ) Northcott missing (feasible, ~tens of lines).

# ============ A6 10-ROUND SYNTHESIS (R1-R4, all genuine content) ============
# A6-height rational TORSION FINITENESS (= mordell_weil_fg dependency) is BUILDABLE. Pieces:
#  (a) xRep_two_nsmul_same_dup: x(2P)=dupNumH/dupDenH projectively — EC formula grind (bounded)
#  (b) resultant_dupNum_dupDen = Δ² (ring+b_relation), ≠0 from IsElliptic → coprime → Bezout
#  (c) dup_bezout + integer estimates → doubling lower bound logHeight(xRep 2P)≥4·logHeight(xRep P)−C
#  (d) xProj finite fibers + Northcott.comp_of_finite_fibers + rat_P1_logHeight_northcott (base, feasible)
#  (e) torsion_finite_of_doubling_lower: orbit-max + doubling closure → hX(P)≤C/3 → finite (AIRTIGHT, no canonical ht)
# Genuinely-NEW Mathlib pieces (all feasible, NOT deep gaps): (a) EC dup formula, (c) Bezout int estimates,
#  (d) base ℙ¹(ℚ) Northcott. MUCH smaller than canonical heights / full Mordell-Weil.
# → building this DISCHARGES the mordell_weil_fg axiom (replace rational_torsion_finite_alias source).
#   Campaign: 2 custom axioms → 1 (only no_rational_17 Mazur-pillar remains).
