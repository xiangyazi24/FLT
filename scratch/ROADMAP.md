# Mazur |T|≤16 Formalization — Progress Report

## Status: 0 sorry, 12 axioms, 30+ commits

### Infrastructure Built (all 0 sorry)

#### Integer Descent Proofs
- **Descent20a4.lean**: y²=x³+x²-x has integer solutions only at x∈{-1,0,1}
- **DescentN16.lean**: y²=x³-x²-x has integer solutions only at x∈{-1,0,1}

#### 2-Descent Selmer Computation for Curve 20.a4 (COMPLETE)
φ-direction (E→E', 6 obstructions):
- **SelmerD2.lean**: C_2 trivial (2-adic descent)
- **Selmer20a4.lean**: C_5 trivial (5-adic descent)
- **SelmerNeg.lean**: C_{-2}, C_{-5} trivial (p-adic descent)
- **SelmerD10.lean**: C_{10} trivial (5-adic + coprimality)
- **SelmerNeg10Phi.lean**: C_{-10} trivial (5-adic + coprimality)
Result: Sel^φ = {1,-1}, dim = 1

φ̂-direction (E'→E, 6 obstructions):
- **SelmerDual.lean**: C'_{-1}, C'_{-5}, C'_{-2}, C'_{-10} trivial (real obstruction)
- **SelmerDualD2.lean**: C'_2 trivial (2-adic descent)
- **SelmerDualD10.lean**: C'_{10} trivial (2-adic + coprimality)
Result: Sel^{φ̂} = {1,5}, dim = 1

Rank formula: rank = 1+1-1-1 = 0 ■

#### Isogeny Infrastructure
- **Isogeny20a4.lean**: Forward + dual 2-isogeny with affine equation proofs
- **E20GoodReduction.lean**: |E(F_3)|=6, |E(F_7)|=6, discriminant checks

#### Group Theory
- **GroupTheory.lean**: ZMod embedding, card, square containment
- **RootsOfUnity.lean**: Only roots of unity in Q are ±1

#### Modular Curve Point Counts
- **X1_13_PointCount.lean**, **X1_17_PointCount.lean**: native_decide

#### Bug Fix
- **DescentBridgeN12.lean**: Degenerate set {-2,1,2}→{-2,0,1,2,4} (old version was FALSE)

### Gap to Axiom Discharge

The 12 remaining axioms all require algebraic geometry infrastructure not in Mathlib:

1. **Descent exact sequence**: connecting Selmer groups to Mordell-Weil rank
   (would enable: Selmer computation → rank 0 → integrality → axiom 5)

2. **Weil pairing**: e_m: E[m]×E[m]→μ_m non-degenerate and Galois-equivariant
   (would enable: axiom 3)

3. **Tate normal form + Kubert table**: parametrization of curves with torsion
   (would enable: axioms 9-12)

4. **Structure theorem for E[n]**: rank(E[n]) = 2 over algebraic closure
   (would enable: axiom 2 from axiom 1)

5. **Mordell-Weil theorem**: E(Q) finitely generated (axiom 1)

6. **Mazur cyclic bound**: no rational point of order ≥ 17 (axiom 4 — the hardest)
