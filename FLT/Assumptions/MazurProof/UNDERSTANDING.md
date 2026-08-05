# UNDERSTANDING.md — Mazur |T| ≤ 16 Proof Framework

## Goal

Prove `(AddCommGroup.torsion (E⁄ℚ).Point : Set).ncard ≤ 16` for any
elliptic curve `E` over `ℚ`, replacing the axiom in `FLT/Assumptions/Mazur.lean`.

## Proof Structure

```
                    ┌─────────────────────┐
                    │  |T| = m * n ≤ 16   │
                    └──────────┬──────────┘
                               │
                 ┌─────────────┴─────────────┐
                 │                           │
          m = 1: |T| = n              m = 2: |T| = 2n
          need n ≤ 16                 need n ≤ 8
                 │                           │
                 │                    ┌──────┴──────┐
                 │                    │             │
              Axiom 3:            Axiom 3:      Axiom 4:
           n ≤ 16 from         n ≤ 16 from    n ≤ 8 from
          "no order ≥17"      "no order ≥17"  "no ℤ/2×ℤ/n
                                               n∈{10,12,14,16}"

          ┌──────────────────────────────────────────┐
          │        Weil pairing → m ≤ 2              │
          │                                          │
          │  Axiom 1: full m-torsion → prim root     │
          │  RootsOfUnity: prim root in ℚ → m ≤ 2   │  ← PROVED
          └──────────────────────────────────────────┘

          ┌──────────────────────────────────────────┐
          │      Torsion structure: T ≅ ℤ/m × ℤ/n   │
          │                                          │
          │  Axiom 2a: T is finite                   │
          │  Axiom 2b: T has rank ≤ 2                │
          │  Axiom 2c: first factor gives full tors  │
          └──────────────────────────────────────────┘
```

## Dependency Graph (discharge order)

```
Level 0 (DONE):
  RootsOfUnity.lean  ← real proof, no axioms

Level 1 (pure group theory, ~1000 LOC):
  Axiom 2c (first_invariant_factor_full)
    depends on: finite abelian group structure theorem (Mathlib)
  
Level 2 (EC arithmetic, ~5000 LOC each):
  Axiom 2a (rational_torsion_finite)
    depends on: good reduction injection (EC reduction API)
  Axiom 2b (rational_torsion_two_generated)
    depends on: E[N] ≅ (ℤ/N)² over algebraic closure
  Axiom 1 (weil_pairing_primitive_root)
    depends on: Weil pairing construction, divisor theory

Level 3 (explicit certificates, ~10000 LOC):
  Axiom 4 (no_Z2_cross_Zn_forbidden)
    depends on: Kubert/Tate normal form parametrization
    discharge via: obstruction curve rational points
      N=10: LMFDB 20.a4, rank 0, MW = ℤ/6ℤ
      N=12, 14, 16: similar obstruction curves (Sage certificates)

Level 4 (deep Mazur, ~100000 LOC):
  Axiom 3 (no_rational_point_of_order_ge_17)
    depends on: modular curves X₁(n), Jacobians, Eisenstein ideal,
                OR explicit X₁(n) certificates for n = 17..28 + formal immersion for p ≥ 29
```

## Files

```
FLT/Assumptions/MazurProof/
  RootsOfUnity.lean     ← PROVED: ℚ roots of unity = {±1}
  Axioms.lean           ← All axiom declarations (Groups A-D)
  TorsionBound.lean     ← Main theorem: |T| ≤ 16 from axioms
  MazurProof.lean       ← Module import file

Future (as axioms are discharged):
  TorsionStructure.lean ← Axiom 2 discharge
  WeilPairing.lean      ← Axiom 1 discharge
  NoncyclicCert.lean    ← Axiom 4 discharge (+ Sage certificates)
  CyclicBound.lean      ← Axiom 3 discharge (the big one)
```

## Key Design Decisions

1. **Axioms as seams, not sorry.** Each axiom is a self-contained mathematical
   theorem that can be independently proved and tested. This matches Buzzard's
   own FLT methodology (see FLT/Assumptions/README.md).

2. **Opaque predicates.** `HasFullRationalTorsion`, `HasRationalPointOfOrder`,
   etc. are opaque Props. This prevents the skeleton proof from depending on
   implementation details of the torsion API, which is still developing.

3. **Card = m * n in the structure axiom.** Without this, converting between
   the group-theoretic structure and `Set.ncard` requires substantial API work.
   It's a mathematical consequence of the structure theorem, not an extra
   assumption.

4. **Weil pairing returns a primitive root, not directly m ≤ 2.** This is the
   natural mathematical seam — the Weil pairing produces the root, and the
   ordered-field argument (already proved) gives m ≤ 2. Bundling them would
   make the axiom harder to discharge.

## Noncyclic Certificate Details (Axiom 4)

For each n ∈ {10, 12, 14, 16}, the proof that ℤ/2 × ℤ/n ⊄ E(ℚ)_tors follows:

1. Parametrize all E/ℚ with full 2-torsion + order n/gcd(2,n) point
   (Kubert family / Tate normal form)
2. The parametrization gives a one-parameter family over ℚ
3. Full 2-torsion imposes a discriminant-square condition
4. This defines an obstruction curve C over ℚ
5. Show C(ℚ) consists only of degenerate/cuspidal points

For N=10: obstruction curve is LMFDB 20.a4 (y² = x³ + x² - x),
MW group = ℤ/6ℤ (rank 0), rational points u ∈ {-1, 1, 3} are all cusps.

## Progress Log (2026-06-17 automode session)

### Proved (0 sorry, 0 axiom — real Lean theorems):
1. **RootsOfUnity.lean**: isPrimitiveRoot_rat_order_le_two, rat_root_of_unity_eq_one_or_neg_one
2. **TorsionFinite.lean**: torsion_set_finite_of_fg (Noetherian ℤ-module → torsion submodule f.g. → finite)
3. **GroupTheory.lean**: zmod_prod_contains_square ((ℤ/m)² ↪ ℤ/m × ℤ/n when m|n)
4. **CyclotomicLayer.lean**: primitive_root_forces_le_two interface
5. **ZModEmbedding.lean** (scratch): same as GroupTheory content

### Proved from axioms (skeleton):
6. **TorsionBound.lean**: mazur_torsion_bound (|T| ≤ 16 from 6 axiom seams)

### Verified computation:
7. **DescentObstruction.lean**: N=10 2-isogeny local obstructions via native_decide
8. **ObstructionN10Complete.lean**: curve 20.a4 rational point verification

### Axiom seams remaining:
- mordell_weil_fg (standard, in TorsionFinite.lean)
- weil_pairing_primitive_root (needs EC Weil pairing or det = χ_m)
- no_triple_two_torsion (2-rank ≤ 2; needs E[2] ≅ (ℤ/2)²)
- no_rational_point_of_order_ge_17 (Mazur cyclic classification or X_1(n))
- no_Z2_cross_Z10 (needs obstruction curve 20.a4 rank-0 certificate)
- no_Z2_cross_Z12 (needs obstruction curve rank-0 certificate)

### Sorry seams remaining:
- finite_abelian_two_invariant_factors (pure group theory, now a def with sorry)
  Statement is mathematically correct. Proof needs: primary decomposition →
  CRT combination → invariant factor form. ~500 LOC estimated.

### Key design decisions:
- Refactored cyclic bound to Mazur classification (n ∈ {1..10,12}) — eliminates N=14, N=16 noncyclic cases
- Weil pairing axiom seam at the primitive-root level (not m ≤ 2 directly)
- TorsionFinite discharge: mordell_weil_fg → Noetherian → f.g. torsion → finite (real proof)
- N=10 descent: LMFDB 20.a4, MW = ℤ/6ℤ, rank 0, local obstructions mod 125
- **2026-06-18**: Fixed false axiom `finite_abelian_two_invariant_factors`.
  Original hypothesis only constrained odd primes (2 < p), leaving 2-rank
  unconstrained → FALSE for (ℤ/2)³. Added `h_two_rank` parameter and new
  axiom `no_triple_two_torsion` for the EC application. Net axiom count
  unchanged but mathematical correctness restored.

## Progress Log (2026-07-10 order-11 exclusion)

- Proved the general Tate-normal-form bridge for a marked point of order
  greater than three.
- Proved the explicit division-polynomial identity
  `ψ₁₁(0,0)=b⁴⁰F₁₁(b,c)` and the exact-order equivalence at the Tate origin.
- Proved the rational algebra map from `F₁₁=0` to the noncuspidal locus on
  `Y²=X³+8X²+16X+16`.
- For the Billing--Mahler model `η²=ξ³-432ξ+8208`, proved denominator
  normalization, the finite exceptional-point enumeration, and the complete
  parity tail from the three descent coefficient equations.
- `CyclicExclusion11.lean` now has one exact residual theorem,
  `billing_mahler_global_descent`; its Tate/moduli `sorry` is closed.
- Added `BillingMahlerField.lean` with no `sorry`: it constructs the cubic
  number field, proves the integral basis and discriminant `-44`, class number
  one, unit rank one, and the four unit squareclasses represented by
  `1,-1,epsilon,-epsilon`.  It also proves the Mordell norm identity, extracts
  a unit times a square from an ideal square, selects the `epsilon` class from
  positive norm plus nonsquareness, and derives the three Billing--Mahler
  coefficient equations.
- Consequently the remaining order-11 seam no longer assumes the coefficient
  system or the unit squareclass.  In the ordinary branch it asks only for the
  ideal generated by the primitive cubic factor to be an ideal square and for
  that factor to be nonsquare; the exceptional branch is the fixed-curve
  Lutz--Nagell alternative.
- The earlier claim that Q4012/Q4013 supplied a complete finite 2-descent was
  false: the local table and scalar/norm compatibility were not proved.
- UISAI2 target build passed.  See the repository-root `HANDOFF.md` for the
  exact residual signature and server synchronization state.

## Progress Log (2026-07-18 order-49 exclusion)

- **Structural approach (DONE, 0 sorry, 0 axiom, builds in 41s):**
  1. `TateOrder49Factor.lean` (345 lines): proves `preΨ'₄₉(0) = b⁸⁰⁰ * bracket₄₉`
     by unrolling the `preΨ'_odd` recurrence through intermediate G-polynomials
     (G23, G24, G25, G26). Each step is a bounded rewrite + ring (degree ≤ 40).
     No brute-force computation.
  2. `TateOrder49Bridge.lean` (62 lines): proves the equivalence
     `RawOrder49TateObstruction ↔ ExplicitOrder49Obstruction` where the explicit
     form is `bracket₄₉(b,c) = 0` with `b ≠ 0`, `F₇ ≠ 0`, `W` elliptic.
- The remaining axiom in `CyclicExclusion49.lean` (`no_raw_order49_tate_obstruction`)
  now reduces to proving: no rational (b,c) satisfies
  `bracket₄₉(b,c) = 0 ∧ F₇(b,c) ≠ 0 ∧ b ≠ 0 ∧ W(b,c) elliptic`.
- Key insight: the bridge works directly with the unfactored bracket₄₉ (degree 160).
  The factorization `bracket₄₉ = F₇ * F₄₉` (where F₄₉ is the genus-69 modular curve)
  is NOT needed for the bridge — only for the eventual rational-point analysis.
- Previous brute-force approaches (staged ring1, F₄₉ as explicit 3526-monomial
  polynomial) were abandoned: they required 9.5-17 GB elaboration and 2+ hours.

## Progress Log (2026-07-19 N18 fix + N49 descent)

### N18 build fixes
- **N18VpiWrapper.lean**: Fixed two Mathlib API breakages:
  - Line 57: `vpiGood_three` — added `; norm_cast` for WithTop ℤ coercion
  - Lines 72-76: `Ideal.mem_of_liesOver` — rewrote from `.mpr` term-mode to tactic-mode
- **N18PackageII.lean**: Fixed two Mathlib API breakages:
  - Line 209: `ordPi_finset_sum_gt_or_zero` — added missing `{ι : Type*}` parameter
  - Line 841: `three_pow_nsmul_data` zero case — replaced broken `simpa using ⟨...⟩`
    with `refine ⟨?_, ?_, ?_⟩` + individual `simpa [pow_zero]` subgoals
- Full chain N18VpiWrapper → N18PackageII → N18GoodModelAssembly → CyclicOrderAssembly
  now builds. The `no_order_18` theorem is proved (`sorry`-free on N18 route).

### N49 discharge strategy (from ChatGPT co-design Q140)
- **Key insight**: X₀(49) ≅ E₄₉ (Cremona 49a1, LMFDB 49.a4), genus 1, rank 0.
  Equation: y² + xy = x³ - x² - 2x - 1, Δ = -7³, j = -3375.
- **E₄₉(ℚ) = {O, (2,-1)} ≅ ℤ/2ℤ** — both points are cusps of X₀(49).
- **Proof via 2-isogeny descent**:
  - Split model: V² = U³ + 21U² + 112U (U² + 21U + 112 irreducible, disc = -7)
  - 2-isogenous: Z² = X³ - 42X² - 7X
  - φ-Selmer = {1, 7}: d<0 killed at real place (positive definite form);
    d=2,14 killed at p=2 (mod 32)
  - φ̂-Selmer = {1, -7}: all non-survivors killed at p=2 (mod 16)
  - Both Selmer groups size 2 = |kernel| → rank = 0
- **File `X049DescentObstruction.lean`**: Contains all 12 local obstruction theorems
  (6 for φ, 6 for φ̂). Archimedean obstruction for d<0 proved via completing the
  square; 2-adic obstructions via `native_decide` on ZMod 32/16.
- **Remaining for N49 discharge**:
  1. Wire the descent obstructions to prove E₄₉(ℚ) = {O, (2,-1)}
  2. Build explicit Tate(b,c) → X₀(49) coordinate map (the bottleneck —
     needs Vélu quotient + Hauptmodul computation, dispatched to ChatGPT)
  3. Show the map's image avoids both cusps when b≠0, F₇≠0
  4. Wire to `no_raw_order49_tate_obstruction`

### Definitive endpoint inventory (source-rebuilt audit, 2026-08-05)

The authoritative command is
`#print axioms MazurProof.mazur_torsion_bound` after rebuilding every changed
dependency from source in order.  The endpoint currently depends on exactly
**6 custom axioms**, plus the Lean built-ins `propext`, `Classical.choice`,
and `Quot.sound`.  It does **not** depend on `sorryAx`.

| # | Primitive axiom | File | Mathematical content |
|---|-----------------|------|----------------------|
| 1 | `C13Sextic_affine_x_is_cuspidal` | `CyclicExclusion13` | Every rational point on the optimized genus-two `X₁(13)` model is cuspidal |
| 2 | `no_F17_rational_solution` | `CyclicExclusion17` | The nondegenerate Tate equation for order 17 has no rational solution |
| 3 | `no_F19_rational_solution` | `CyclicExclusion19` | The nondegenerate Tate equation for order 19 has no rational solution |
| 4 | `no_explicit_order25_obstruction` | `CyclicExclusion25` | The explicit primitive order-25 obstruction has no rational point |
| 5 | `no_raw_order49_tate_obstruction` | `CyclicExclusion49` | The primitive order-49 Tate obstruction has no rational point |
| 6 | `no_prime_order_ge_23` | `CyclicOrderAssembly` | Uniform formal-immersion exclusion for prime orders at least 23 |

The previous seven-item table was stale in three ways:

- `exists_rational_two_isogeny_quotient` is now a theorem from
  `VeluTwoIsogeny`, so orders 20 and 24 are clean.
- The endpoint uses the direct Tate Diophantine axioms for orders 17 and 19,
  not the older `order17_to_kernel_root` and `order19_to_kernel_root` bridge
  names.
- The primitive N13 seam is `C13Sextic_affine_x_is_cuspidal`;
  `no_F13_rational_solution` is a derived theorem.

The audit initially reported `sorryAx` because several `.olean` files were
older than their proved sources.  Rebuilding
`VeluTwoIsogeny → CyclicExclusion20 → CyclicOrderAssembly` removed that
artifact.  Rebuilding `CyclicExclusion13` likewise exposed the correct
primitive N13 axiom.  Endpoint audits must therefore compare source and
`.olean` timestamps and rebuild stale dependencies before recording results.

**Fully discharged from the endpoint dependency graph:**

- Orders 11 and 18 are theorems via the Billing--Mahler and N18 descent
  routes.
- All composite exclusions 14, 15, 16, 20, 21, 24, 27, and 35 are clean;
  theorems for 25 and 49 depend only on the named rational-point axioms above.
- The Vélu two-isogeny quotient used for orders 20 and 24 is clean.
- `mordell_weil_fg` is not used; torsion finiteness follows from the cyclic
  order bound and the proved real torsion bound.
- The two tracked `sorry`s in `KubertBridgeN16.lean` are not reachable from
  `mazur_torsion_bound`; the endpoint uses the clean cyclic `X₁(16)` route
  and different noncyclic exclusions.

#### N13 analysis note
F₁₃(b,c) is bivariate (degree 10 in c, monic leading coeff -1; degree 7 in b;
20 terms, total degree 11). The degree-7 homogeneous part is -b(b-c)⁶. Over
𝔽₂, 𝔽₃, 𝔽₅: the only solution with b≠0 is the empty set. This rules out
integer solutions via infinite descent, but rational solutions require the full
genus-2 Chabauty argument (X₁(13) has Jacobian of rank 0, MW ≅ ℤ/19ℤ).

## Progress Log (2026-08-05 N13 low-degree spreads)

- The irreducible quadratic branch is now closed without a project axiom:
  the finite, reciprocal, and vertical two-chart cases all prove that the
  canonical divisorial hull is invertible.
- `N13QuadraticFractionalSpread.lean` packages reducible and irreducible
  quadratic graphs behind one interface: every degree-two selected graph has
  an invertible integral fractional ideal whose generic extension is exactly
  its Mumford graph ideal.
- `N13DegreeOneFractionalSpread.lean` gives the analogous degree-one
  interface.  An integral point uses the canonical divisorial hull, while an
  escaping point uses the affine ideal of its explicit invertible two-chart
  line.
- `N13FiniteAffineTwoChart.lean` removes the properness asymmetry in that
  statement.  An invertible affine ideal with finite quotient has an
  invertible infinity-chart closure: a monic equation for the affine
  coordinate reflects to an equation with constant coefficient one, so the
  infinity uniformizer is a unit modulo the closure and localization
  patching applies.  In particular, every integral affine point graph has an
  honest proper two-chart line with its literal affine ideal.
- Combining that closure with the existing escaping point line proves that
  every selected degree-one graph has a proper `TwoChartLine` whose affine
  generic fibre is exactly the selected Mumford graph.
- `N13IntegralAffinePointSpecialClass.lean` computes the other fibre of the
  integral point family at the affine-ideal level.  Coefficientwise reduction
  sends the literal integral point ideal exactly to the linear Mumford graph
  of the reduced special point.  The corresponding point-indexed special
  class is explicitly normalized as that point plus the positive-infinity
  anchor.  What is still missing is a general geometric specialization map
  from a raw `TwoChartLine` (or its Cartier divisor) proving that its special
  divisor equals this anchored divisor; the target and its affine support are
  no longer ambiguous.
- `N13LowDegreeFractionalSpread.lean` now exhausts the Padé bound
  `natDegree ≤ 2` and gives every selected graph one invertible integral
  fractional spread with the exact normalized generic Mumford ideal.
- `N13ArbitraryLowDegreeFractionalSpread.lean` removes the Padé restriction:
  every balanced two-adic Mumford graph, and in particular the finite graph
  of the chosen low-degree representative of every rational Picard class,
  has such an exact invertible affine spread.
- The reciprocal infinity-chart recovery is now proper in both rank-two
  basis branches.  A recovered vertical graph packages its invertible
  affine closure and infinity ideal into a `TwoChartLine`, and exact
  contraction identifies its generic affine ideal with the original
  Mumford graph.  Together with the existing horizontal recovery, every
  integral reciprocal quadratic has an exact proper two-chart spread.
- Consequently every irreducible quadratic graph now has a proper two-chart
  line whose generic affine ideal is literally the graph ideal.  The finite
  affine branch uses the general infinity-closure theorem, while the
  escaping branch uses reciprocal horizontal-or-vertical recovery.  No
  finite-versus-reciprocal properness dichotomy remains.
- `N13QuadraticTwoChartSpread.lean` closes the reducible branch as well.
  Every two-adic affine point now has a valuation-independent proper point
  line, and tensoring two such lines realizes split secant and repeated-root
  tangent graphs.  The split-or-irreducible dichotomy therefore gives every
  balanced quadratic Mumford graph, and every selected degree-two graph, a
  proper `TwoChartLine` with its exact generic affine graph ideal.  Together
  with the degree-one result, the low-degree proper-spread algebraic layer is
  closed.
- The chart-level `nInf` factor is now explicit.  The two integral points
  `(t,v)=(0,0)` and `(0,-1)` give the positive- and negative-infinity
  `TwoChartLine`s.  Natural tensor powers of the positive line are trivial
  on the affine chart, so tensoring them onto any proper spread preserves
  its exact affine generic ideal.  What remains is the semantic theorem
  identifying these local lines with the corresponding oriented Picard
  classes; affine ideals alone cannot distinguish the two infinity points.
- `N13InfinitySpecialPointClass.lean` now computes the same two infinity
  sheets in the special Abel model.  The negative-infinity point together
  with the fixed positive anchor is the canonical hyperelliptic fibre,
  whereas two positive anchors are noncanonical.  Thus their anchored
  special classes are provably distinct without forgetting the sheet
  coordinate.
- Proper reduction of every escaping affine point is now proved to land on
  exactly one of those two infinity sheets.  Consequently its anchored
  special class is either the regular anchor-double class or the canonical
  class.  The remaining `abel_reduces` input is not this point
  classification: it is the geometric special-fibre theorem identifying
  the reduction of the explicit proper point line with the anchored class
  of the point reduced from the same infinity-chart lift.
- The general finite-support closure now supplies the missing
  infinity-chart extension whenever the chosen affine ideal has finite
  quotient.  This has been instantiated for integral point graphs and the
  finite irreducible quadratic branch.  The reducible quadratic constructors
  are now consolidated behind the same proper-line interface.  What remains
  is identifying the positive-infinity tensor factor with the
  representative's oriented `nInf` coordinate and identifying chartwise
  special reduction with a literal divisor on the completed special curve.
- Mathlib at the pinned revision has no exported descent constructor turning
  two affine module sheaves and an overlap isomorphism into a module sheaf on
  `Scheme.GlueData.glued`.  The shortest rigorous specialization bridge is
  therefore ring-theoretic: reduce both ideals of a `TwoChartLine`, retain
  their proved special-overlap equality, identify that chart pair with the
  canonical chart ideals of an `EffectiveDivisorTwo`, and separately retain
  the explicit infinity orientation.  A general relative Picard functor or
  Cartier-divisor formalization is not presently a prerequisite.
- `N13TwoChartSpecialRestriction.lean` implements the first step of that
  bridge.  It maps both chart ideals through the literal reduction maps and
  proves that their extensions remain equal on the special overlap by the
  already proved overlap-reduction square.  The output is a concrete
  `ChartPair`; the remaining special-fibre task is to identify selected such
  pairs with canonical chart ideals of explicit effective divisors.
- `N13SpecialDivisorCharts.lean` constructs those canonical chart pairs.
  A finite special point with `x=0` is supported only on the affine chart, a
  finite point with `x=1` is written compatibly on both charts under
  `x=t⁻¹` and `y=x³v`, and an infinity point is supported only on the
  infinity chart.  Multiplying two point pairs descends through `Sym2`, so
  every `EffectiveDivisorTwo` now has literal compatible affine and infinity
  ideals.  The remaining task is to equate the chartwise reduction of each
  selected integral proper line with the pair of its intended special
  divisor.
- `N13TwoChartPicardRealization.lean` packages the resulting two-fibre
  semantics without postulating a relative Picard functor.  Its `Data`
  retains a proper line, an explicit oriented infinity integer, a literal
  `EffectiveDivisorTwo`, and exact equalities for both reduced chart ideals.
  The oriented generic class and special Abel class are then definitions.
  Constructing `Data` for the selected corrected low-degree lines is now the
  precise specialization producer boundary.
- `N13InfinityLineSpecialRestriction.lean` proves the first concrete
  producer cases.  The positive and negative integral infinity point ideals
  reduce exactly to `(t,v)=(0,0)` and `(0,1)`, respectively; the two sheets
  remain distinct.  The positive point is proved equal to the fixed special
  anchor, and chartwise restriction is proved compatible with tensor
  products and natural powers.  Consequently the special chart ideals of
  every positive `nInf` correction are now formal powers of the anchor ideal.
- `N13EscapingPointSpecialRestriction.lean` closes both special-chart fields
  for every nonintegral affine point.  The cleared affine generator
  `1-t₀x` reduces to `1`, while the infinity graph reduces to the point
  selected by proper reduction.  Tensoring once with the positive-infinity
  line therefore gives exactly the canonical chart pair of
  `s(reducedPoint, specialAnchor)`.  This completes the special-fibre
  realization of the escaping degree-one branch; only its oriented generic
  comparison remains before constructing full Picard `Data`.
- `N13FiniteAffinePointInfinityClosure.lean` closes the finite degree-one
  special branch.  It identifies the abstract contracted infinity closure
  with the explicit weighted ideal `(1-at, v-bt³)`.  The proof shows that
  this ideal is already `t`-saturated because `a` is the inverse of `t`
  modulo the ideal; no primality or principality assumption is used.
  Reduction then gives `⊤` when `ā=0` and `(t-1,v-b̄)` when `ā=1`, exactly
  the two canonical point-chart cases.  After tensoring once with positive
  infinity, both reduced chart ideals equal those of
  `s(reducedPoint, specialAnchor)`.  Thus the special-fibre realization of
  every degree-one point line is complete; its oriented generic comparison
  is the remaining degree-one `Data` field.
- All public spread theorems named above pass scoped compilation, bypass
  scanning, and `#print axioms`; their only dependencies are `propext`,
  `Classical.choice`, and `Quot.sound`.
- The remaining N13 mathematical providers are a concrete
  `N13SpreadClassifier.SpreadData`, compatibility of rational Abel classes
  with reduction (`abel_reduces`), and separatedness of the reduced kernel.
  In the current design, the last item reduces to constructing
  `RationalKernelDoublingData`, including its compatible disk-pair
  realization and integral first-jet doubling law.  Once these providers
  exist, the final affine-cuspidality wiring is thin.
- `N13RationalKernelDoublingAdapter.lean` sharpens the separatedness
  boundary.  The transition-square quadratic estimate is already proved.
  It remains to produce a centered near-base integral Mumford graph for
  each kernel class and to compare the chosen representative of `2 • z`
  with the squared transition modulo the moving coordinate ideal squared.
  Those two inputs now assemble directly into
  `RationalKernelDoublingData` and hence `NSeparated`.
- The near-base producer is itself reduced further in the same adapter.
  It suffices to give each kernel class a balanced representative of the
  translated class `z + basePic` whose canonical contraction maps literally
  to the selected special ideal.  `exists_diskPair_class_eq` then supplies
  the centered disk pair and the exact Picard realization automatically.
- The representative choice can now be removed entirely: use the canonical
  balanced normal form `normalize (z + basePic)`.  A
  `CanonicalMappedSpecialFamily` stores only the literal mapped-special
  equality for those normal forms.  It recovers the centered disk pairs and
  reaches separatedness once the single family-level
  `FirstJetDoublingCompatibility` statement is supplied.
- Earlier axiom inventories in this file describe historical snapshots and
  must not be treated as current.  Use a fresh `#print axioms` audit of the
  assembled theorem before reporting the remaining global Mazur boundary.
