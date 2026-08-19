# Mazur Proof Status — 2026-08-18 (v2, after Newton polygon analysis)

## Overall: `mazur_cyclic_order_bound_assembled` in CyclicOrderAssembly.lean

Theorem proved modulo 4 endpoint axioms (+ 5 dead-code sorries).
Mordell-Weil (`mordell_weil_fg`) intentionally kept.

## Axiom 1: `C13Sextic_affine_x_is_cuspidal` — N13

**Status: 1 sorry remaining (class_eq_iff)**

- 283 sorry-free files provide full infrastructure (Picard group, Abel-Jacobi, Mumford coordinates, etc.)
- N13DischargeWiring.lean written: wires endpoint with kernel = ⊥
- **h₁/h₃ gap CLOSED**: For trivial kernel, z ranges only over {0}; at z=0, F.pair(0) = basePair (by SmallMumfordRigidity), so cross-coefficient polynomial = 0
- **class_eq_iff GAP**: Injectivity of the specialization map on J(Q) = Z/19Z at p=2

### Proof of class_eq_iff (mathematical argument, not yet formalized)
- Kernel of J(Q) → J(F_2) is a 2-group (Néron model / formal group theory)
- J(Q) = Z/19Z has no 2-torsion (19 is odd)
- Therefore kernel = {0}, map is injective
- Alternative: |J(F_5)| = 19 = |J(Q)|, so J(Q) ≅ J(F_5) directly (but infrastructure uses p=2)

### Computed Jacobian orders
| p | |C(F_p)| | |J(F_p)| | 19 divides? |
|---|---------|---------|-------------|
| 3 | 6 | 3 | No |
| 5 | 6 | **19** | **Yes (exactly!)** |
| 7 | 8 | 57 = 3·19 | Yes |
| 11 | 12 | 133 = 7·19 | Yes |

## Axiom 2: `no_explicit_order25_obstruction` — N25

**Status: Active development (172+ commits). Don't touch.**

Architecture: Koszul resolution + twisting sheaves + Frobenius orbits. Ambient Koszul-to-curve seam is closed.

## Axiom 3: `no_raw_order49_tate_obstruction` — N49

**Status: Local approach BLOCKED. 8/9 charts closed, global argument needed.**

### Bihomogeneous parity analysis (p=2)
- 6/9 charts excluded by direct mod-2 evaluation
- Chart #1 excluded by Newton face (face sum odd)
- Chart #5 excluded by Newton face (face sum odd)
- Chart #2: genuine Q₂-points exist (Q5293 verified Hensel-liftable)

### Newton polygon of H_49
- 9 vertices, all with coefficient ±1 (alternating sign)
- Cyclotomic face (slope 3/2, 7 terms = Φ_7 quotient) locally obstructed (Φ_7(1)=7≡1 mod 2)
- 7 binomial faces: Hensel-liftable, corresponding to genuine order-49 2-adic points
- Multi-prime CRT {2,3,5}: same 3 charts zero at every prime (structural)

### Computed H_49 data
- 3526 terms over Z, 1603 terms mod 2
- Edges: left=c^133, top=b^7, right=-1
- H_49(t,t) = -t^157 (diagonal pure monomial)
- 10 monomials above the original face (including (2,144) with h=-1)

### Required: global argument
Options: modular curve X_1(49)(Q)=cusps, descent on composition curve, MW sieve

## Axiom 4: `no_prime_order_ge_23` — p≥23

**Status: Hardest axiom. No infrastructure. Needs formal immersion/Eisenstein ideal.**

## Dead-Code Sorries (5)
All confirmed dead — not transitively used by the assembled theorem.

## Priority
1. **N13**: Single sorry (class_eq_iff), mathematical argument known
2. **N49**: Needs strategy revision (local→global)
3. **N25**: Active development
4. **p≥23**: Long-term

## Key Discovery: Circularity Break Path for N13

The code routes class_eq_iff → canonical family → GeometricData → Chart → NSeparated.
But GeometricData's ingredients are ALL independent of class_eq_iff:
- pair : K → DiskPair (from Abel chart section, independent)
- pair_zero (trivial)
- pair_injective (from SmallMumfordRigidity, independent)
- law : PolynomialLaw (from N13TwoAdicAbelChartLaw, independent)

Direct path: GeometricData(independent) → Chart → Chart.separated → NSeparated K 2
Then: TwoSurjective(proved) + NSeparated + |J₂|=19 → reduction_injective → class_eq_iff

The circularity is code routing, not mathematics.
