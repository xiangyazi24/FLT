# N49 Newton Polygon Analysis — 2026-08-18

## Computations verified (Python, integer arithmetic)

- H_49 has 3526 terms over Z, 1603 terms mod 2
- Max degree: 98 in b, 147 in c
- h_{0,133} = 1, h_{98,0} = -1, h_{7,147} = 1 (all edges single monomials)
- h_{0,0} = h_{0,147} = h_{98,147} = 0 (corner zeros)

## Bihomogeneous parity analysis (p=2)

6/9 charts excluded directly (mod-2 evaluation nonzero).
3 charts ZERO at every prime (structurally, from h_{0,0}=h_{0,147}=h_{98,147}=0):
- Chart #1: (0,1)×(0,1) → v_2(b)≥1, v_2(c)≥1
- Chart #2: (0,1)×(1,0) → v_2(b)≥1, v_2(c)≤-1
- Chart #5: (1,0)×(1,0) → v_2(b)≤-1, v_2(c)≤-1

Multi-prime CRT {2,3,5} checked: same charts zero at every prime. CRT doesn't help.

## Newton face analysis

### Chart #1 — EXCLUDED ✓
Face: 19i + 14j = 1862, connecting (0,133) to (98,0)
8 lattice points: coefficients [1, ?, ?, ?, ?, ?, ?, -1]
Face sum at (1,1): odd → excluded at first stage

### Chart #5 — EXCLUDED ✓
Face: 21i + 13j = 2058, connecting (98,0) to (7,147)
Face sum at (1,1): odd → excluded at first stage

### Chart #2 — OPEN (multi-stage needed)

Newton polygon of H_49 in the (α>0, β>0) quadrant has 9 vertices:
| Vertex | h | Sign |
|--------|-----|------|
| (0,133) | 1 | + |
| (2,144) | -1 | - |
| (7,147) | 1 | + |
| (15,142) | -1 | - |
| (26,129) | 1 | + |
| (38,111) | 1 | + |
| (55,82) | -1 | - |
| (75,45) | 1 | + |
| (98,0) | -1 | - |

All vertices have coefficient ±1 (unit, nonzero mod every prime).
Each vertex alone gives nonzero initial form → vertex directions excluded.

Edge analysis (8 edges):
| Edge | Slope α/β | Terms | Sum mod 2 | Status |
|------|-----------|-------|-----------|--------|
| (0,133)→(2,144) | 11/2 | 2 | 0 | OPEN |
| (2,144)→(7,147) | 3/5 | 2 | 0 | OPEN |
| (7,147)→(15,142) | 5/8 | 2 | 0 | OPEN |
| (15,142)→(26,129) | 13/11 | 2 | 0 | OPEN |
| (26,129)→(38,111) | 3/2 | 7 | 1 | EXCLUDED ✓ |
| (38,111)→(55,82) | 29/17 | 2 | 0 | OPEN |
| (55,82)→(75,45) | 37/20 | 2 | 0 | OPEN |
| (75,45)→(98,0) | 45/23 | 2 | 0 | OPEN |

7 edges OPEN: all have exactly 2 nonzero lattice points (the endpoints)
with coefficients +1 and -1, so the face polynomial is ±(u^a v^b - u^c v^d),
which always vanishes at (u,v)=(1,1). This is a structural property of H_49's
alternating ±1 vertex pattern.

## Approach for closing Chart #2

The face polynomials u^a v^b - u^c v^d factor as u^a v^b (1 - u^{Δi} v^{Δj}).
For odd (u,v), 1 - u^{Δi} v^{Δj} ≡ 0 mod 2 always.
The v_2 depends on (Δi, Δj):
- For edge (0,133)→(2,144): 1 - u^2 v^{11}, v_2 = 1 when v ≡ 3 mod 4.
  At β≥2: face/2 dominates near-face → excluded.
  At β=1: need near-face contribution.
  Requires multi-stage Newton descent or algebraic argument.

## Alternative approaches
1. Modular curve: X_1(49)(Q) = cusps (this IS Mazur's theorem for N=49)
2. Composition identity: use preΨ'_49 = preΨ'_7(x(7P)) · preΨ'_7^49
3. Complete multi-stage Newton descent at p=2 for 7 edges
4. Algebraic structure: all Newton polygon vertices have |h|=1, suggesting
   a resultant/norm interpretation

## Scripts
- n49_newton_face.py: F_2[b,c] division polynomial recursion + Newton face (mod 2)
- n49_integer.py: Z[b,c] computation for face coefficients over Z
- n49_verify.py: Verification of above-face monomials and near-face analysis
- n49_multiprime.py: Multi-prime CRT + full Newton polygon computation

## Update: Q5293 confirms local approach is BLOCKED

ChatGPT Q5293 (independent verification) confirms:
- The 7 binomial Newton polygon edges are **Hensel-liftable** at p=2
- Each lifts to a genuine Q_2-point of exact order 49 on a nonsingular curve
- Only the cyclotomic face (slope 3/2, Φ_7 quotient) provides local obstruction
- **No amount of p-adic refinement can close Chart #2**

### Why the cyclotomic face works but binomial faces don't

The 7-term face at slope 3/2 (edge (26,129)→(38,111)) is the image of the
cyclotomic polynomial Φ_7(T) = 1+T+T^2+T^3+T^4+T^5+T^6 under the projection
of H_49 / F_7. At T=1: Φ_7(1) = 7 ≡ 1 mod 2 (nonzero). This is the ONLY
face whose initial form doesn't vanish mod 2.

The binomial faces (h₁·m₁ - h₂·m₂ with h₁=+1, h₂=-1) always vanish at
(u,v)=(1,1): |+1-1|=0 mod 2. And the Hensel derivative is nonzero, so they lift.

### Revised strategy

The N49 proof requires **global input**. Three options:
1. **Modular curve X_1(49)(Q) = cusps** via Jacobian rank-0 + Chabauty
2. **Descent on the composition curve** using preΨ'_7(x(7P)) = 0
3. **Mordell-Weil sieve** using the 8 locally-closed charts + global J structure

ChatGPT Q5294 dispatched for genus computation and composition-identity approach.
