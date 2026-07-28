# DOCTRINE — Campaign to discharge remaining 6 axioms

## Main Goal

Eliminate ALL 6 custom axioms from `mazur_cyclic_order_bound_assembled`.
Current status: 6 custom axioms + 3 standard (propext, Classical.choice, Quot.sound).

## The 6 Axioms (verified Jul 26)

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 1 | `C13Sextic_affine_x_is_cuspidal` | CyclicExclusion13 | The standard `X₁(13)` sextic has affine x-coordinate 0 or -1 |
| 2 | `no_F17_rational_solution` | CyclicExclusion17:21 | F₁₇(b,c)=0 has no ℚ-solution with b≠0 |
| 3 | `no_F19_rational_solution` | CyclicExclusion19:21 | F₁₉(b,c)=0 has no ℚ-solution with b≠0 |
| 4 | `no_prime_order_ge_23` | CyclicOrderAssembly:100 | Formal immersion on X₀(p) for p≥23 |
| 5 | `no_explicit_order25_obstruction` | CyclicExclusion25:47 | F₂₅(b,c)=0 with b≠0 ∧ F₅≠0 impossible |
| 6 | `no_raw_order49_tate_obstruction` | CyclicExclusion49:43 | preΨ'₄₉(0)=0 ∧ preΨ'₇(0)≠0 impossible |

### Cleared (complete)

- `exists_rational_two_isogeny_quotient` — DISCHARGED via VeluTwoIsogeny (5d11f7e944)
- The old N13 `no_F13_rational_solution` axiom — REPLACED by a theorem:
  Tate parameters → Kubert raw model → optimized genus-two model → standard sextic
  (`N13TateBridge`, `N13CurveModel`, commit b42fbe9294)
- Old bridge axioms `order17_to_kernel_root` / `order19_to_kernel_root` — REPLACED
  by direct `no_F17/F19_rational_solution` (bridge files deleted)
- N18 import cycle fixed, sorry closed
- N15/N21/N35 fully proved (0 sorry, 0 axiom)
- N27 fully proved (three-descent)
- N14 fully proved (Z₂×Z₁₄ obstruction)

### Non-critical axioms (NOT on `mazur_cyclic_order_bound_assembled` path)

- `mazur_prime_torsion_bound` (CyclicOrderReduction:31) — vestigial, superseded by `mazur_prime_torsion_bound_sub` theorem
- `mazur_cyclic_order_bound` (OrderReduction:19) — vestigial, superseded by `mazur_cyclic_order_bound_assembled`
- `mordell_weil_fg` (TorsionFinite:14) — standalone, not on cyclic path

### Non-critical sorry (NOT on critical path)

- `N18AddCongr.lean:303` — sorry in `add_congr`
- `KubertBridgeN16.lean:342,361` — sorry in `kubert_C16_discriminant_data` and `EN16_point_of_Phi16_and_disc`
- `N18GoodModelZParam.lean:42,44` — sorry in z-parametrization

## Key Computational Results (Jul 26)

### F_n polynomials (preΨ'_n(0) = b^{power} · product of F_k)

Using exact Lean preΨ' recurrence from TateOrder49Factor.lean:
- F₅ = b-c (1 term)
- F₇ = c³+bc-b² (3 terms)
- F₁₃: 20 terms, total degree 10, IRREDUCIBLE over ℚ, min degree 6
  - Leading form (degree 6): bc(b-c)⁴ → (0,0) is 6-fold singularity
  - Factored form: (b-c)(c³-b²+bc)³ + bc(b-c-c²)⁴
- F₁₇: 53 terms, total degree 19, IRREDUCIBLE over ℚ
- F₁₉: 80 terms, total degree 24, IRREDUCIBLE over ℚ
- F₂₅: 234 terms, total degree 40, MONIC in b (degree 25, leading coeff = 1)
  - Degree-25 homogeneous part: b⁵(b-c)²⁰

### Mod-p obstruction table (bivariate F_n(b,c), b≠0 in 𝔽_p²)

| F_n | p=2 | p=3 | p=5 | p=7 |
|-----|-----|-----|-----|-----|
| F₁₃ | 0 | 0 | 2 | 1 |
| F₁₇ | 0 | 0 | 0 | 0 |
| F₁₉ | 1 | 2 | 3 | 8 |

For F₂₅(b,c) = 0 with b≠0 in 𝔽_p²:
| p=2 | p=3 | p=5 | p=7 |
|-----|-----|-----|-----|
| 0 | 0 | 0 | 0 |

### p-adic analysis (Jul 26)

**F₁₃ does NOT have a 2-adic or 3-adic obstruction.** The tree of
approximate ℤ_p solutions (with b∈pℤ_p, near the 6-fold singularity at
(0,0)) keeps growing at each precision level. At level n (mod p^n), the
number of candidates with v_p(F₁₃) ≥ 3n grows as ~O(n²). The singular
point (0,0) has tangent cone bc(b-c)⁴, preventing the p-adic tree from
dying.

**Implication:** Proving `no_F13_rational_solution` cannot use a single
local (p-adic) obstruction. Need either:
(a) Brauer-Manin obstruction (combination of local data), or
(b) Chabauty-Coleman (genus 2, Jacobian rank ≤ 1), or
(c) Explicit descent (adapt N=11 Billing-Mahler approach), or
(d) Modular curve theory (X₁(13)(ℚ) = cusps by Mazur)

**F₁₇, F₂₅ status:** Not yet analyzed p-adically. F₂₅ has even deeper
singularity (degree-25 part = b⁵(b-c)²⁰), likely also no simple local
obstruction.

### Why mod-p alone is insufficient

F₁₃, F₁₇, F₁₉ are bivariate in (b,c) and NOT weighted homogeneous.
The mod-p table shows no 𝔽_p solutions for certain primes, but a
rational solution (b₀,c₀) with b₀≠0 can have v_p(b₀)>0, reducing
to the singular point analysis above.

For F₂₅: monic-in-b plus mod-p eliminates INTEGER solutions (Gauss's
lemma forces rational roots of a monic integer polynomial to be integers).
But c₀ need not be integer for general rational solutions.

## Avenues

### (a) N25 via monic structure → `no_explicit_order25_obstruction`

F₂₅ is MONIC in b (degree 25, leading coeff 1). 234 terms, total degree
range 25–40. Degree 38 in c, leading c-coefficient = b².

**Structural data (Jul 26):**
- Degree-40 (projective top) form: b²c³⁴(b⁴+b³c+b²c²+bc³+c⁴) = b²c³⁴Φ₅(b,c)
- Degree-25 (affine bottom) form: b⁵(b-c)²⁰
- F₂₅(0,c) = -c³⁵, F₂₅(b,0) = b²⁵, F₂₅(b,b) = 5b⁴⁰
- ALL projective solutions mod 2,3,5 are at infinity (cusps)
- F₂₅ is NOT monic in c (leading c-coeff = b²), so "c must be integral"
  argument fails

**Substitution t=c/b, H(b,t) = F₂₅(b,tb)/b²⁵:**
- H has deg_b = 15, deg_t = 38, 234 terms
- H(0,t) = (t-1)²⁰, H(b,1) = 5b¹⁵
- Leading b¹⁵ coefficient: t³⁴·Φ₅(t) where Φ₅ = t⁴+t³+t²+t+1

**Newton polygon of H(b,1+s) at (0,0):**
- Edge 1: (0,20)→(1,14), slope -6, initial form = u+1 (root u=-1)
- Edge 2: (1,14)→(15,0), slope -1, initial form = (u+1)¹⁰·(5u⁴+10u³+10u²+5u+1)
  - 10 branches with u=-1 (rational initial value)
  - 4 branches with irrational u (from irreducible quartic) — cannot be rational
- Total: 11 potentially rational branches + 4 definitely irrational = 15 (= deg_b)
- All branches are cusps; proving none extend to affine rational points
  requires Chabauty-Coleman or descent

**Conclusion:** Monic structure helps computationally (integer sieve for
integer solutions) but does NOT force c to be integral. Full rational-point
enumeration requires Jacobian/Chabauty infrastructure not in Mathlib.

Terminal: axiom replaced by theorem (requires new Mathlib infrastructure).

### (b) N49 → `no_raw_order49_tate_obstruction`

Reduces to F₄₉(b,c) = 0 with b ≠ 0 (degree ~157, genus ~69).
Too high genus for direct methods.

Alternative: birational map to Cremona 49a1 (rank 0), enumerate rational points.

Terminal: axiom replaced by theorem.

### (c) N13 descent → `no_F13_rational_solution`

X₁(13) is genus 2. F₁₃ is irreducible over ℚ, 20 terms, total degree 10.
2-adic/3-adic obstructions do NOT exist (verified computationally).

**Structural reductions completed Jul 27:**
- Kubert substitution `b=rs(r-1), c=s(r-1)` factors the Tate condition into
  the low-degree raw equation.
- The birational map to `y²+(x³+x²+1)y=x²+x` is proved on the full
  nondegenerate Tate chart, including all denominator exclusions.
- Completing the square with `X=-x-1`, `Y=2y+x³+x²+1` gives
  `Y²=X⁶+4X⁵+6X⁴+2X³+X²+2X+1`; the four affine cusps lie over `X=0,-1`.
- A generic smooth monic-sextic Mumford layer is in progress.  The N13 sextic
  is monic, degree six, and separable by a short Bézout identity with its
  derivative.  This is the intended base for the fixed Jacobian 2-descent.
- The two Laurent embeddings at infinity are now explicit.  For every
  `p(X)+q(X)Y`, the product of the two branches is the quadratic norm
  `p²-q²f`, and the minimum branch order is
  `-max(deg p,deg q+3)`.  Thus cancellation at one infinity is detected at
  the other; no leading-coefficient table is needed.
- The rational diamond action is the visible `C₆` action
  `x ↦ -1/(x+1)`.  Its order-three quotient is the rational conic
  `z²=u²+4u+8`, with cubic fibers.  This proves structurally that the quotient
  is genus zero, but also that it cannot by itself classify the rational
  points.  There is no non-hyperelliptic involution over `ℚ`, hence no
  rational elliptic quotient shortcut.
- Over `ℚ(i)`, the sextic is the norm of the cubic
  `A+iB`, where `A=X³+2X²-X-1` and `B=2X(X+1)`.  The associated sextic field
  has class number one, unit rank two, and a 16-class global square-class
  envelope after the primes above `2` and `13` are imposed.  These PARI data
  are recorded only as a reproducible guide; the remaining proof obligation
  is the actual local-image theorem for those classes.
- The direct Abel--Jacobi map is now proved injective without a global
  `NormalFormData` assumption.  The proof clears both numerator directions
  of a principal relation, applies the two-infinity norm-degree rigidity,
  and recovers the monic Mumford `u` by contraction of scaled ideals.
- The local square-class calculation has a structural correction: after the
  2-, 13-, and real conditions, the two representatives are `1` and
  `e2*a*q`, but the unit identity
  `(e2*a*q)*(ζ*e1*a)^2=13` makes the latter a rational scalar.  They are
  already equal in `L*/(L*² ℚ*)`, the natural fake-descent target.  The next
  formal step is therefore the quotient target and this identity, not a
  search for a further local obstruction.
- Modulo three the four affine points are proved from
  `f(x)=1-x(x+1)` and Frobenius, not enumeration.  Together with the two
  infinity points, these are exactly the six cusp reductions.

The only remaining N13 axiom is now the fixed sextic rational-point theorem,
not the high-degree Tate polynomial.

Possible approaches:
(i) Complete the fixed genus-two weak 2-descent from the 16 global classes.
(ii) Formalize the Mazur--Tate 19-isogeny/fppf descent (more structural but
substantially larger).

The rational elliptic-quotient route has been ruled out by the proved
automorphism structure.

Terminal: axiom replaced by theorem.

### (d) N17/N19 → `no_F17_rational_solution` / `no_F19_rational_solution`

F₁₇ and F₁₉ are irreducible over ℚ (genus 5 and 7 respectively).
Direct Chabauty requires Jacobian rank < genus, which may not hold.
Need Chabauty-Coleman or étale descent.

Alternative: prove via modular curve theory (X₁(17), X₁(19) rational
points are cusps by Mazur).

Terminal: axiom replaced by theorem.

### (e) Formal immersion → `no_prime_order_ge_23`

Deepest axiom. Needs Hecke algebra, Eisenstein quotient, formal immersion.
Mazur 1977 §5. Leave for last.

Terminal: axiom replaced by theorem (long-term campaign).

## Execution Order

1. **NOW:** (c) N13 — formalize the fake square-class quotient and collapse
   the two local survivors by the rational-scalar identity
2. **NEXT:** connect the resulting weak descent to Jacobian finiteness and
   the six-cusp reduction conclusion
3. **THEN:** (b) N49 after an explicit Tate-to-`X₀(49)` coordinate bridge exists
4. **LATER:** (a) N25 (needs a deep rank-zero input), (d) N17/N19, then the prime tail
6. **LAST:** (e) formal immersion

## Build Status

- VeluTwoIsogeny: BUILDING (original code, no modifications, ~55 min)
- CyclicOrderAssembly: PENDING (depends on VeluTwoIsogeny → CyclicExclusion20)
- Dead code: PrimeExclusion17Bridge.lean and PrimeExclusion19Bridge.lean DELETED
- New files: TateOrder{13,17,19}.lean, CyclicExclusion{13,17,19}.lean (0 sorry each)
