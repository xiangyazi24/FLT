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
**4 custom axioms**, plus the Lean built-ins `propext`, `Classical.choice`,
and `Quot.sound`.  It does **not** depend on `sorryAx`.

| # | Primitive axiom | File | Mathematical content |
|---|-----------------|------|----------------------|
| 1 | `C13Sextic_affine_x_is_cuspidal` | `CyclicExclusion13` | Every rational point on the optimized genus-two `X₁(13)` model is cuspidal |
| 2 | `no_explicit_order25_obstruction` | `CyclicExclusion25` | The explicit primitive order-25 obstruction has no rational point |
| 3 | `no_raw_order49_tate_obstruction` | `CyclicExclusion49` | The primitive order-49 Tate obstruction has no rational point |
| 4 | `no_prime_order_ge_23` | `CyclicOrderAssembly` | Uniform formal-immersion exclusion for prime orders at least 23 |

The previous inventories were stale in four ways:

- `exists_rational_two_isogeny_quotient` is now a theorem from
  `VeluTwoIsogeny`, so orders 20 and 24 are clean.
- The endpoint previously used direct Tate Diophantine seams for orders 17
  and 19, not the older `order17_to_kernel_root` and
  `order19_to_kernel_root` bridge names; both direct seams are now discharged.
- The primitive N13 seam is `C13Sextic_affine_x_is_cuspidal`;
  `no_F13_rational_solution` is a derived theorem.
- `TateOrder17Quotient.no_F17_rational_solution` is now a theorem, so the
  order-17 Tate seam is no longer an endpoint axiom.

The audit initially reported `sorryAx` because several `.olean` files were
older than their proved sources.  Rebuilding
`VeluTwoIsogeny → CyclicExclusion20 → CyclicOrderAssembly` removed that
artifact.  Rebuilding `CyclicExclusion13` likewise exposed the correct
primitive N13 axiom.  Endpoint audits must therefore compare source and
`.olean` timestamps and rebuild stale dependencies before recording results.

**Fully discharged from the endpoint dependency graph:**

- Orders 11, 17, 18, and 19 are theorems via the Billing--Mahler, explicit
  order-17 quotient, N18 descent, and degree-three quotient/descent routes.
- All composite exclusions 14, 15, 16, 20, 21, 24, 27, and 35 are clean;
  theorems for 25 and 49 depend only on the named rational-point axioms above.
- The Vélu two-isogeny quotient used for orders 20 and 24 is clean.
- `mordell_weil_fg` is not used; torsion finiteness follows from the cyclic
  order bound and the proved real torsion bound.
- The two tracked `sorry`s in `KubertBridgeN16.lean` are not reachable from
  `mazur_torsion_bound`; the endpoint uses the clean cyclic `X₁(16)` route
  and different noncyclic exclusions.

#### Discharged N19 endpoint

The N17 seam is fully discharged.  `TateOrder17Quotient.lean` normalizes the
Tate equation, constructs an explicit rational map through two genus-one
models to the proved `X₀(17)` equation, classifies the image using
`X017RationalPoints`, and eliminates every possible fibre.  This is a direct
algebraic implication from `F17 b c = 0`; it does not rely on an unformalized
modular interpretation or twist/kernel transport.

The former N19 endpoint axiom has been replaced by a source theorem.
The Tate-normal-form bridge produces `b`, `c`, `b ≠ 0`, the residual equation
`F19 b c = 0`, and an elliptic Tate curve.  The completed proof establishes
the stronger global nonvanishing statement for every rational pair with
`b ≠ 0`.

`PrimeExclusion19.lean` proves that a fixed degree-nine CM kernel polynomial
has no rational root, but the completed endpoint does not use that alternative
route.  Instead it uses the universal algebraic quotient and direct
rational-point classification described below.

The universal algebraic quotient is now explicit.
`N19SutherlandModels.lean` identifies the repository `F19` with Sutherland's
raw equation, proves that every nonboundary raw point lies in the optimized
chart, and verifies a degree-three quotient to
`v²+v=u³+u²+u`.  A compact Bézout identity shows that the zero horizontal
fibre would have optimized coordinate `x=-1`, while the raw equation proves
that this is a boundary point.  `TateOrder19Quotient.lean` assembles these
identities and reduces the broad `F19` nonvanishing theorem to the single
arithmetic statement that every affine rational point on the quotient has
first coordinate zero.

`XDelta19Model.lean` records the quotient curve, its integral short model
`Y²=X³+(2X+4)²`, and the explicit three-isogeny pair.
`XDelta19Descent.lean` completes the first rational-flex descent: a primitive
integral normalization proves that `Y-(2X+4)` is always a rational cube, and
the resulting explicit formulas prove that the dual three-isogeny is
surjective on rational points.  `XDelta19Isogeny.lean` now bundles the
forward map and verifies by the affine chord-and-tangent law, including its
visible three-torsion fibre, that the dual-forward composition is
multiplication by three.

The complementary descent uses the smaller integral model
`Y²=X³+(8X+76)²`.  `XDelta19GoodModel.lean` proves that it is exactly the
previous scaled quotient under `s=9X+228`, `t=27Y`; its discriminant is
`-2¹²·19³`, so it has good reduction at three.
`XDelta19GoodIsogeny.lean` constructs its quotient
`t²=s³-3(24s+12)²`, bundles both degree-three maps, and proves that their
dual-forward composition is multiplication by three.  The small constant
`12` is the decisive normalization for the complementary Eisenstein descent:
unlike the earlier scaled equation, its quotient factorization has no
split prime above nineteen.  `XDelta19GoodDescent.lean` now completes the
primitive two-adic normalization on this model.  Its two flex factors have
cube product, can share only the prime nineteen, and therefore give exactly
the three candidate rational cubeclasses `1`, `19`, and `19²`.
`XDelta19GoodDualDescent.lean` completes the complementary Eisenstein
calculation.  It separates conjugate prime factors using the constant `12`,
excludes the `ζ` and `ζ²` unit classes by exact modulo-27 certificates,
expands the remaining cube into an explicit rational preimage, and proves
the forward three-isogeny surjective on rational points of the small
quotient.  Finally, `XDelta19GoodWeakDescent.lean` combines both descents:
translation by `(0,76)` or `(0,-76)` converts the `19` and `19²` classes to
cubes, so every good-model rational point is a threefold multiple up to one
of those two visible three-torsion points.

`XDelta19GoodFormalCore.lean` and
`XDelta19GoodFormalReduction.lean` finish the three-adic endgame.  Explicit
doubling formulas and finite residue certificates force `6P` into every
formal level, and separatedness gives `6P=0`.
`XDelta19GoodRationalPoints.lean` combines this result with weak
three-descent and the absence of nonzero rational two-torsion to prove
`3P=0`; the dual-forward composition then forces every affine good-model
point to have first coordinate zero.
`XDelta19RationalPoints.lean` transports that classification through the
scaled dual and short models to `v²+v=u³+u²+u`, and
`TateOrder19Quotient.no_F19_rational_solution_of_diamond_x_eq_zero` finishes
the Tate residual.  `CyclicExclusion19.no_F19_rational_solution` is therefore
a theorem whose axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

`TateOrder17.exists_tate_parameters_of_order_seventeen_with_j` now preserves
the original curve's `j`-invariant together with ellipticity, exact order,
`b ≠ 0`, and `F17 b c = 0`; the final direct algebraic quotient proof does
not need to reconstruct that certificate.

#### Current N25 foundation

The active endpoint seam remains
`CyclicExclusion25.no_explicit_order25_obstruction`, but the local
rational-point infrastructure is no longer empty.
`RationalPointsN25CanonicalPoints.lean` records the canonical
quadric-cubic model of the genus-four quotient `25.150.4.f.1`, proves that
every canonical point with a zero homogeneous coordinate is one of the five
rational cusps, and gives the exact dense-chart elimination to a plane
sextic with a recovered fourth coordinate.
`RationalPointsN25QuotientAction.lean` verifies an explicit linear
automorphism of order five, its action on the five cusps, the cyclic
augmentation coordinates, and homogeneous invariants of weights two, three,
and five.
`RationalPointsN25QuotientF2.lean` gives kernel-checked exhaustive
classifications over `𝔽₂` and its quadratic extension: the five special
projective points are exactly the cusp classes, and no new class appears
over `𝔽₄`.
`RationalPointsN25QuotientWeil.lean` extends the normalized-projective
enumeration to the first four binary extensions and proves
`#C(𝔽₂)=5`, `#C(𝔽₄)=5`, `#C(𝔽₈)=20`, and `#C(𝔽₁₆)=29` for the canonical
equations.  The cubic field table is certified in that file.  The quartic
field laws are split among
`RationalPointsN25QuotientF16Add.lean`,
`RationalPointsN25QuotientF16Mul.lean`, and
`RationalPointsN25QuotientF16Distrib.lean`, then assembled by
`RationalPointsN25QuotientF16Field.f16_isBinaryFieldTable`; this closes the
finite-field-table seam without `native_decide`.
`RationalPointsN25QuotientSmoothF2.lean` verifies four exact chartwise
Bézout identities for the quadric, cubic, and six two-by-two Jacobian minors.
Its terminal theorem excludes the resulting singularity predicate over every
field of characteristic two, hence in particular over an algebraic closure.
`RationalPointsN25QuotientZeta.lean` converts the four counts through Newton's
identities into the reciprocal polynomial
`1+2T+2T²+5T³+11T⁴+10T⁵+8T⁶+16T⁷+16T⁸` and proves that it evaluates to
`71` at one.  It deliberately does not identify that polynomial with the
curve's zeta numerator or identify `71` with a Jacobian cardinality.
`TateOrder25ParameterAction.lean` proves that the primitive equation forces
`c`, `F6`, and `F7` to be nonzero, verifies `2P=(b,bc)` by the affine group law,
and derives the generator-change parameters
`B₂=bF6³/c⁸`, `C₂=(c⁴+(2b+c²-c)F6)/c⁴` from the actual translation and
Tate scaling.  Equality of all five Weierstrass coefficients is proved, so
these formulas are connected to the stored Tate model rather than being
formal rational-function candidates.  The same file now proves the explicit
multiple formulas for `3P`, `4P`, and
`7P=(bcF6F8/F7²,-b²F6²F9/F7³)` directly from the affine group law; this
replaces the old private scratch-only versions and supplies the actual point
to be normalized for the involution.  It also proves that the Tate origin has
exact additive order 25 on the primitive locus, then uses this exact order to
exclude both remaining normalization factors.  Vanishing of `G14` would give
`14P=0`.  Vanishing of the translated quadratic numerator `H7` would make the
translated origin a flex, hence a point killed by three; transporting back
would give `21P=0`.  Both contradict exact order 25.  Consequently the full
translation and Tate scaling at `7P` is now unconditional on the primitive
locus, with explicit parameters `B₇,C₇` and all five Weierstrass coefficients
checked.
`RationalPointsN25SutherlandBridge.lean` now identifies the literal Tate
source equation with Andrew Sutherland's published affine models.  In raw
coordinates `r=b/c` and `s=c²/(b-c)`, it proves the exact equality
`F25=c¹⁰(b-c)¹⁵ Fraw`.  It then verifies the universal birational optimization
to Sutherland's bidegree-`(8,8)` equation by a denominator-cleared polynomial
identity.  The two specializations
`Fraw(1/(2-s),s)=(s-1)²³/(2-s)¹⁰` and
`Fraw(s²-s+1,s)=-s(s-1)²⁷` prove that both optimization denominators are
nonzero on the primitive Tate locus.  Thus every primitive `F25` solution now
maps, without extra hypotheses, to the checked optimized source model.
`RationalPointsN25CanonicalSourceBridge.lean` closes the previously missing
model comparison directly.  Singular's Gorenstein adjoint ideal for the
degree-twelve projective closure has a twelve-dimensional degree-nine
canonical space.  The exact `⟨7⟩` diamond involution on the function field has
`(+1,-1)` dimensions `(4,8)` there; the residual doubling action identifies
the invariant four-space with the already stored order-five canonical action.
The resulting four degree-nine polynomials map Sutherland's optimized source
to the stored canonical model.  Lean independently verifies literal pullback
identities for both the quadric and cubic and exposes the composite theorem
`tateCanonicalCoordinates25_onCanonical` on the original primitive Tate
locus.  It also proves that the optimized source `y` coordinate is neither
zero nor one there, using the raw diagonal identity
`Fraw(r,r)=r⁴(r-1)¹⁷`.  A kernel-checked Bezout resultant between the first
and fourth adjoint cores reduces simultaneous vanishing to a monic degree-ten
polynomial with no root modulo two.  Consequently the composite canonical
coordinate vector is formally proved nonzero on every primitive Tate
solution.  A second exact resultant between the source equation and the third
canonical coordinate is `(y-1)¹²p₁₀(y)`, so that coordinate is nonzero as
well.  It excludes cusp classes A, C, and E; the first/fourth nonvanishing pair
excludes B and D.  Hence the composite is formally noncuspidal on the entire
primitive Tate locus.  This route does not require the formerly missing
birational map to the LMFDB degree-eleven plane.
`RationalPointsN25TateCanonicalBridge.lean` now supplies the
denominator-free target-side lift
`(x,z,w) ↦ (xD,-N,zD,wD)`.  Its cubic vanishes identically and its quadric
pullback is exactly the stored plane sextic.  The same file now contains the
official degree-eleven LMFDB plane equation for `X_{\pm1}(25)` (label
`25.300.12.j.1`) and an explicit four-coordinate degree-six map from that
source model to the stored genus-four canonical model.  Its two defining
equations are certified by the unconditional polynomial identities
`Q(Φ) = -C F₁₁` and `K(Φ) = -W H₆ F₁₁`.  This remains an independently checked
target-side model comparison, although the direct adjoint map above now
bypasses its formerly missing source-plane identification.  Because every listed cusp
has a zero among its first
three canonical coordinates, the denominator-free sextic lift is already
noncuspidal when `x,z,D,N` are nonzero; the plane coordinate `w` needs no
separate certificate.

All production files above pass scoped compilation.  Axiom audits of the
finite-field laws, point counts, Bézout certificates, smoothness-predicate
consequence, Hilbert-polynomial calculation, and Frobenius-polynomial
calculation report only `propext`,
`Classical.choice`, and `Quot.sound`.  They are not yet imported by
`CyclicExclusion25`: the source-side model bridge, base-point exclusion, all
five projective cusp fibres, and the raw finite-field arithmetic are closed.

The remaining N25 route has three honest geometric/arithmetic layers.  First,
the explicit characteristic-two and characteristic-three Jacobian-minor
certificates must be connected to smooth proper reductions.  The standard
complete-intersection Hilbert-series arithmetic is now certified as `6T-3`,
but the explicit equations still have to be connected to a regular
codimension-two projective subscheme whose scheme-theoretic Hilbert
polynomial is that polynomial.  The formal divisor-count theorem proved below
then turns the checked point counts into
`#Pic^0(C)(𝔽₂)=#Pic^0(C)(𝔽₃)=71`, once its geometric interfaces are
instantiated for the explicit fibres.
Second, one needs a
global statement making `Jac(C)(ℚ)` finite and a two-prime specialization
argument controlling every torsion prime; reduction at two alone does not
exclude rational two-primary torsion.  The current candidates use either the
degree-two map from `X₁(25)` to the quotient or the level-25 newform factor,
whose external source statements are audited below but whose
pullback/newform infrastructure is not yet formalized.  Third, Abel--Jacobi
injectivity must turn the
resulting Jacobian information into the classification that every rational
canonical point is one of the five cusps.  None of these layers is hidden in
the polynomial theorem.

The primary-source audit now fixes the external target precisely.  The
corrected arXiv v2 of Derickx--Etropolski--van Hoeij--Morrow--Zureick-Brown,
*Sporadic cubic torsion*, Theorem 3.1 places `25` in the unconditional
rank-zero range for `J₁(N)(ℚ)`.  Theorem 4.13 and Corollary 4.14 identify the
full rational group with the rational cuspidal subgroup at this level, and
Table 2 gives the single invariant factor `[227555]` (equal to
`5·71·641`).  The associated computation is in
`Sage/torsionComputations.py` of the authors' repository, audited at master
commit `f0c6cf41e156d9d96bebd6b639e1f71208f04b6c`.  These are verified source
facts, not yet Lean providers.  In particular, invoking them still requires a
formal modular-curve/Jacobian quotient theorem.

The smaller factor-local candidate is the exact newform orbit `25.2.d.a`:
the LMFDB source data records dimension four, coefficient field
`ℚ(ζ₁₀)`, and coefficients `a₂=ζ₁₀²-ζ₁₀`, `a₃=-ζ₁₀³`.
`RationalPointsN25NewformEulerCertificate.lean` now checks the complete
four-conjugate norm identity at three and proves
`P₃(T)=1+T-2T²-5T³+T⁴-15T⁵-18T⁶+27T⁷+81T⁸` with `P₃(1)=71`.
The newform identification and Frobenius interpretation remain explicit open
seams.  If supplied, the bounds at two and three control complementary
primary torsion; this corrects the earlier, insufficient single-prime plan.

The direct characteristic-three curve calculation is being rebuilt with a
structure-first proof.  A first attempt normalized the `x=1` chart and split
the `F₈₁` search into many fixed-coordinate truth-table files.  Although those
files could be made kernel-checkable, the method still enumerated an
`81³` Cartesian product, consumed tens of gigabytes per certificate, and
explained no mathematics.  That route is rejected and its generated modules
are not production evidence.  Merely partitioning a finite search does not
turn it into a proof worth maintaining.

There are two successive structural reductions.  First, in characteristic
three the normalized quadric is
`Q = y²+yz-z+(z-1)w`; away from `z=1` it determines `w` uniquely.  The exact
cleared-denominator identity reduces the cubic to
`B(y,z)=y⁴z+yz⁴+y³z-z⁴+y³-y²+z²+z`, while the exceptional divisor
`z=1` is handled separately.  This already changes a three-dimensional point
search into a bivariate residual problem.  Second, over `F₈₁`, which contains
the fifth roots of unity, diagonalizing the proved order-five automorphism
turns the quadric into `u₂u₃=u₁u₄`.  The Segre parametrization
`(u₁,u₂,u₃,u₄)=(ac,ad,bc,bd)` turns the cubic into a four-term
bidegree-`(3,3)` equation.  On its dense chart, with `r=b/a`, `s=d/c`, and the
invariant quotient parameter `t=r²s`, it has Kummer form
`r⁵=-t²(B+ζ²t)/(1+At)`.  The intended `F₈₁` certificate therefore
checks 81 affine quotient parameters and a finite boundary divisor, not
`81²` or `81³` ambient tuples.  The generic elimination and Kummer identities
must be Lean theorems; only their final one-dimensional fibre and boundary
data may be finite certificates.

`RationalPointsN25QuotientKummerThree.lean` now closes the abstract
fifth-power-fibre seam without enumeration.  In a cyclic group of order 80,
the image of `x ↦ x⁵` is exactly the kernel of `x ↦ x¹⁶`: inclusion follows
from `x⁸⁰=1`, and both subgroups have order 16.  Every nonempty fibre is
equivalent to the five-element kernel of the fifth-power map.  Passing between
field roots and unit-group roots therefore proves, for every 81-element field,
that `r⁵=c` has one root when `c=0`, five roots when `c≠0` and `c¹⁶=1`,
and no roots otherwise.  The same file now gives mutually inverse forward and
inverse eigenbasis matrices, proves that the canonical quadric is a nonzero
scalar times `u₂u₃-u₁u₄`, proves rank-one factorization, and derives an exact
affine-cone equivalence between the canonical quadric-cubic intersection and
the Segre cubic.  These are symbolic polynomial and field arguments, not
coordinate enumeration.

`RationalPointsN25QuotientF81Field.lean` closes the former finite-table
semantic seam.  It constructs the polynomial-basis model over `ZMod 3`, proves
the ring laws by coordinatewise `ring` identities, and uses a terminal
80-element certificate only for the prescribed inverse `a⁷⁹`.  Transport to
the existing `F81` table proves that its zero, one, addition, negation,
multiplication, powers, and `f81Inv` are the operations of an actual
characteristic-three field.  `RationalPointsN25QuotientKummerThreeF81.lean`
then identifies the stored cyclotomic root and coefficients with the generic
Kummer model and proves that every executable fibre size is the cardinality
of the actual field equation.  Thus the sum 87 is now a theorem about genuine
Kummer root fibres, not merely a table output.

`RationalPointsN25QuotientKummerThreeProjective.lean` closes the Kummer
projective bookkeeping.  Away from `r=0`, `t=r²s` gives an explicit
equivalence between dense Segre and Kummer solutions.  The cleared Kummer
zero fibre has two points while the dense zero fibre has one, leaving 86
dense points.  The two boundary rulings and their corner contribute one point
each, so the normalized `P¹×P¹` Segre curve has exactly 89 points.  The file
also proves that the old executable normalized-point predicate over `F81` is
literally the canonical quadric-cubic predicate in the transported field.

The underlying projective coordinate equivalence is now also formalized.
The file defines first-nonzero normalization for arbitrary nonzero
four-vectors, proves that normalization differs only by a nonzero scalar,
proves both eigenbasis matrices commute with scaling and preserve
nonvanishing, and packages them as an equivalence of normalized projective
three-space.  Its restriction to the equation loci is now closed as well.
The four normalized Segre charts are proved equivalent to the normalized
determinant quadric by an explicit chartwise inverse.  Homogeneity of the
quadric and cubic then shows that first-nonzero normalization preserves their
zero loci, while the nonzero eigenbasis scalars identify the Segre cubic with
the canonical cubic.  The resulting subtype equivalence proves both the
actual field-valued and legacy executable statements
`#C(F₈₁)=89`.  Thus the characteristic-three fourth-extension point count is
now a theorem about the stored canonical quadric-cubic model, not only about
its Segre parameter space.

`RationalPointsN25QuotientSmallThreeFields.lean` and
`RationalPointsN25QuotientSmallThreeSemantic.lean` close the first three
extension-field semantics without returning to ambient enumeration.  The
quadratic and cubic tables are actual fields: their ring laws are symbolic
polynomial identities over the transported trit field, while finite
calculation is confined to the 8 and 26 nonzero inverse laws.  A single
chartwise equivalence then identifies the normalized canonical curve with the
five pieces of the existing linear-elimination count.  On `z≠1` the quadric
reconstructs `w` uniquely; the exceptional divisor and boundary charts are
literal summands.  Consequently the executable values are now semantic
canonical-model counts
`#C(F₃)=5`, `#C(F₉)=5`, and `#C(F₂₇)=20`.

`RationalPointsN25QuotientZetaThree.lean` combines those counts with the
already semantic `#C(F₈₁)=89`.  The resulting power sums are
`(-1,5,8,-7)`, Newton's identities force coefficients `(1,-2,-5,1)`, and
genus-four reciprocity produces
`1+T-2T²-5T³+T⁴-15T⁵-18T⁶+27T⁷+81T⁸`.  This is proved equal to the
independent four-conjugate newform certificate and has value `71` at one.
The arithmetic second-prime calculation therefore no longer requires a
modular quotient/newform identification.  Its remaining semantic boundary is
geometric: package the explicit fibre as a smooth proper curve, connect its
scheme-theoretic Hilbert polynomial to the certified genus-four arithmetic,
and instantiate the divisor/Picard interfaces described below to conclude
`#Pic^0(C)(F₃)=71`.

`CurveZetaClassNumber.lean` now proves the general arithmetic core rather than
postulating a zeta/Jacobian cardinality theorem.  For finite types of effective
divisors and degree-zero Picard classes, a constant-fibre Riemann--Roch formula
implies that `(1-T)(1-qT)Z(T)` is a polynomial of degree at most `2g` and that
its value at one is exactly `#Pic^0`.  The proof partitions effective divisors
by Picard class, uses geometric-series cardinalities for complete linear
systems, and proves the high-degree coefficient recurrence in formal power
series.  It has no custom axioms.

`RationalPointsN25QuotientClassNumber.lean` specializes this theorem at
`q=3`, `g=4`.  It defines the certified point-count zeta series from the
already proved reciprocal numerator and proves that actual effective-divisor
types, Riemann--Roch fibres, and the Euler-product series equality imply
`#Pic^0=71`.  This makes the remaining boundary explicit rather than hiding it
in a Jacobian-cardinality assumption: construct the actual Picard and
effective-divisor types, prove the Riemann--Roch fibre theorem, and identify
the effective-divisor series with the closed-point/extension-point zeta
series.

The former Euler-product seam has now been replaced by an explicit finite
double count.  `CurveZetaEffectiveDivisors.lean` packages locally finite
positive-degree closed points and constructs effective divisors as finitely
supported multiplicity functions; bounded support and bounded multiplicity
prove that every fixed-degree divisor type is finite.
`CurveZetaMarkedDivisors.lean` marks a closed-point occurrence, its removal
level, and one residue-degree position.  Removing the marked copies is an
explicit equivalence, and grouping its return data by removed degree proves

`n A_n = ∑_(k=1)^n N_k A_(n-k)`

without formal logarithms, coefficient division, enumeration, or a
recurrence hypothesis.  A second explicit equivalence proves that the ghost
coefficient is independent of the temporary coefficient cutoff.

`CurveZetaMiddleRiemannRoch.lean` supplies the shorter genus-four consumer:
summed degree-four Riemann--Roch gives `A_4 = 3 A_2 + #Pic^0`.
`RationalPointsN25QuotientMiddleRiemannRoch.lean` now combines this with the
proved marked-divisor recurrence.  `CurveZetaFrobeniusOrbitGrading.lean`
constructs exact-period orbit classes for an arbitrary finite permutation and
proves structurally that fixed points of its `k`-th iterate are intrinsic
degree-`k` ghost slots.  `RationalPointsN25QuotientThreeBaseChange.lean`
proves that normalized canonical curve points commute with coefficient-field
maps.  Finally,
`RationalPointsN25QuotientFrobeniusOrbits.lean` embeds the four semantic
fields in `𝔽_(3^12)`, identifies each degree-`d` field with the actual roots of
`X^(3^d)-X` by an embedding plus the polynomial root bound, descends fixed
normalized projective coordinates chart by chart, and constructs the four
required curve-point/Frobenius-fixed-point equivalences.  No curve point
cardinality is used in these equivalences.

The common finite field contains every orbit of degree at most four because
`1,2,3,4` divide twelve; it is not claimed to contain closed points of all
higher degrees.  The resulting grading is therefore named and consumed as a
degree-at-most-four model.  The concrete middle Riemann--Roch theorem now has
no orbit-classification input: the checked counts force `A_2=15` and
`A_4=116` directly from this Frobenius grading.  Its remaining inputs are the
degree-two/degree-four Picard class maps, complete-linear-system fibre
cardinalities, the residual equivalence, genus-four Riemann--Roch, and the
identification of these orbit-defined effective divisors with the actual
divisors of the smooth projective curve.  The new declarations compile and
their axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

`RationalPointsN25QuotientSmoothF3.lean` now closes the characteristic-three
Jacobian-rank calculation over every field, hence over an algebraic closure.
On the regular `x`-chart, two differentiated elimination identities turn the
`yw` and `zw` minors into the two partial derivatives of the residual; an
exact Bézout certificate forces any common residual critical point onto the
excluded divisor `z=1`.  That divisor has its own quadratic certificate.  On
the `y`-chart the cubic factors as `zw(1+z-w)`, and its two branches are
excluded by explicit minors; the last two charts have a minor identically
equal to one.  This is a symbolic chart proof with no finite-field
enumeration.  What remains is not pointwise nonsingularity, but the Mathlib
scheme-level packaging of this complete intersection as smooth, proper, and
genus four, followed by the geometric instantiation of the proved divisor-zeta
class-number theorem.

`RationalPointsN25QuotientHilbert.lean` closes the arithmetic core of the
genus computation without pretending to supply that scheme bridge.
`RationalPointsN25QuotientTwoKoszul.lean` supplies the exact ungraded
resolution behind the calculation, and
`RationalPointsN25QuotientTwoGradedKoszul.lean` upgrades it in every total
degree to
`0 → S(-5)_n → S(-2)_n ⊕ S(-3)_n → S_n → A_n^{pres} → 0`.
The upgrade uses uniqueness of homogeneous decomposition to show that a
nonzero homogeneous factor can have a homogeneous product only when the other
factor has the complementary degree.  Thus every ungraded syzygy witness is
forced into degree `n-5`; no dimension argument or monomial enumeration is
used.  The standard degree-two/degree-three shifted numerator expands as
`1-T²-T³+T⁵`; Mathlib's Hilbert-polynomial formula then gives `6T-3`, and
the curve convention `P(n)=deg(C)n+1-g` gives the constant-term value
`g=4`.  The file also proves the eventual coefficient formula `6n-3` for
the formal Hilbert series.  The next module proves that `(Q,C)` is homogeneous,
extracts homogeneous coefficients from every ideal relation, and applies the
first isomorphism theorem to identify each presented cokernel with the literal
degreewise image in `S/(Q,C)`.  A further structural kernel argument proves
that these images form an internal direct sum; multiplication of homogeneous
representatives therefore installs the actual quotient `GradedAlgebra`, with
explicit formulas for its degree projections and a surjective graded quotient
map from `S`.  The resulting `Proj` is now constructed, together with its
canonical morphism to binary projective three-space, exact pullback formulas
for projective basic opens, an identification of its degree-zero ring with
`F_2`, and its structure morphism to `Spec F_2`.  Surjectivity of a graded
ring map is now proved to survive every homogeneous localization; Zariski
locality therefore makes this canonical morphism a closed immersion.  Finite
generation over the degree-zero ring also makes the structure morphism proper.
What remains in the projective bridge is to identify its local coordinate
rings and ideal sheaf explicitly, sheafify the shifted
resolution, and identify the scheme-theoretic Hilbert polynomial with the
certified one.  The local
Mathlib source has
general `Smooth`, `Proj`, and properness machinery, but no projective-curve
genus API, no general Picard/Jacobian of a higher-genus curve, and no ready-
made curve divisor/Riemann--Roch API.  The formal class-number consequence of
those missing geometric objects is now proved in
`CurveZetaClassNumber.lean`; the finite closed-point/effective-divisor Euler
recurrence is additionally proved in `CurveZetaMarkedDivisors.lean`.

`RationalPointsN25TwoPrimeReduction.lean` proves the remaining elementary
endgame: if a finite cardinal divides both `2^a·71` and `3^b·71`, it divides
`71`.  The future specialization layer therefore needs only to produce those
two precise divisibility hypotheses.  The subsequent
`RationalPointsN25ReductionCardinality.lean` closes the finite-group layer
between specialization and those hypotheses.  For an arbitrary homomorphism
of finite additive groups it proves the exact kernel-range order formula and
the resulting bound by the kernel order times the target order.  In
particular, two reduction maps with kernel orders `2^a` and `3^b` and target
orders `71` already force the source order to divide `71`.  Thus the remaining
specialization seam is now purely geometric: construct the maps and prove
those kernel and special-fibre cardinality statements.

`RationalPointsN25DegreeTwoPullback.lean` closes the next finite-group step
in the degree-two quotient route.  A finite group whose order divides `71`
has injective doubling.  Therefore any homomorphism `pull` admitting a map
`norm` with `norm (pull x) = 2·x` is injective.  The combined terminal theorem
first obtains the odd-order bound from the two reductions and only then
cancels doubling; it therefore avoids the circular argument that assumes
absence of two-torsion in order to derive that same absence.  The remaining
input here is again genuinely geometric: construct Jacobian pullback and norm
for the checked double cover and prove the degree-two composition formula.

The older
`N25LecacheuxIntegrality.lean` and
`N25LecacheuxSieve.lean` scratch experiments do not currently compile and
do not contain the advertised final Newton-polygon theorem; they must not be
counted as proved N25 infrastructure.

The local computational inventory includes Sage 10.9 and Singular 4.4.1 in
the `sage` micromamba environment.  Earlier notes treating those systems as
unavailable were stale; the direct N25 adjoint computation above was performed
with this installed environment and then reduced to kernel-checkable Lean
polynomial identities.

`X017Model.lean` now verifies the concrete genus-one equation
`y²+xy+y=x³-x²-x-14`, its discriminant `-17⁴`, the rational variable changes
to `Y²=X(X²+30X+289)` and its standard two-isogeny dual, and an explicit
point of exact order four.  This closes the model/visible-torsion algebra but
does not by itself assert the still-missing modular interpretation.
`X017TwoTorsion.lean` proves that the only rational points killed by two on
the standard model are infinity and `(0,0)`, constructs an explicit
equivalence with `Bool`, and obtains two-torsion cardinality exactly two.
This is the sharp torsion input for the eventual `E(ℚ)/2E(ℚ)` rank-zero
criterion.
`X017ExactSequence.lean` now proves the sharpened abstract descent layer.
If the left isogeny quotient has representatives zero and one element killed
by the dual map, the first exact-sequence arrow vanishes, so `G/2G` injects
into the right endpoint quotient.  It also generalizes the N15 rank criterion:
for a finitely generated abelian group, the inequality
`|G/2G| ≤ |G[2]|` forces free rank zero.  The N17-specific producers still
missing at the time this layer was introduced were the two concrete
isogeny-coset exhaustions and finite generation of the rational point group.
The later files listed below supply all three producers.
`X017IsogenySequence.lean` now supplies the concrete additive homomorphisms
required by that abstract layer.  It conjugates the already bundled general
Vélu map and dual map through the explicit N17 source and target
equivalences, proves that their composition is multiplication by two, and
bridges the forward homomorphism back to the standard-coordinate `pointMap`.
The distinguished target representative killed by the dual is proved to be
the point `(0,0)` of exact order two.  The other visible target point
`U=(64,0)` is not in the dual kernel: its dual image is the nonzero source
kernel point.  Q3806 also confirmed that the left two-representative cover
and the right quotient bound are logically independent arithmetic inputs;
neither may be inferred from the other.
`X017Descent.lean` now proves the first arithmetic half of the right-endpoint
classification.  For every nonzero affine source point, denominator clearing
and squarefree-core extraction restrict the first coordinate to squareclass
`1` or `17`; positivity of `x²+30x+289=(x+15)²+64` removes both negative
classes.  At this intermediate stage the `17` class still had to be
converted into the chosen `T`-coset; `X017SecondCoset.lean` performs that
translation and closes the quotient cover.
`X017FirstCoset.lean` proves the corresponding target squareclass
classification.  A squarefree core first leaves `±1` and `±2`; the latter
two classes lead to explicit homogeneous quartics and are eliminated by a
three-stage two-adic parity descent.  The implementation uses only small
kernel-checked `ZMod 8` certificates between honest integer divisions, and
concludes that every nonzero target first coordinate is a square or a
negative square.  `StandardTwoIsogenyPreimages.lean` and the remainder of
`X017FirstCoset.lean` supply the generic square-coordinate preimage and the
translation by the target kernel `(0,0)`.
`StandardTwoIsogenyPreimages.lean` now proves that generic preimage theorem.
For a target point with `x=r²≠0`, it constructs the source point with
coordinates
`p=(r²-a-y/r)/2` and `q=rp`, and verifies the standard Vélu formula
coefficient-independently.  `X017FirstCoset.lean` combines it with the target
squareclass theorem and the identity
`x(Q+(0,0))=-256/x(Q)`.  A negative square therefore becomes a square after
translation by the target kernel.  This proves the first full concrete
two-coset exhaustion, makes the left exact-sequence arrow zero, and makes the
right arrow injective.  The source quotient modulo the dual image is a
logically separate arithmetic input; it is closed by the next layer rather
than inferred from the completed target cover.
`StandardTwoIsogenyDualHom.lean` closes the bundled-map seam without
unfolding the outer short-Weierstrass construction.  Applying the already
additive standard map to the standard dual lands on the twice quotient; the
variable change `(x,y)↦(x/4,y/8)` scales it back to the source and is proved
pointwise equal to `dualPoint`.  Thus the explicit dual formula is now a
genuine additive homomorphism.  The generic preimage file also constructs a
dual preimage of every nonzero square source coordinate.
`X017SecondCoset.lean` uses the correct order-four point
`T=(17,136)`.  For `x(P)=17r²` and `x(P)≠17`, the chord through `P` and
`-T=(17,-136)` gives
`x(P-T)=((y+8x)/(r(x-17)))²`.  The cases `x=0` and `x=17` are handled by the
visible points `K,T,-T`.  This proves the independent source cover by the
dual image and its `T` translate.  The quotient therefore has at most two
elements, the source modulo doubling has at most two elements, and combining
both isogeny covers gives the exact `{0,T}` cover modulo doubling required by
the height descent.
`X017HeightDescent.lean` specializes Mathlib's general descent theorem to a
two-element representative set `{0,T}` modulo doubling.  It proves finite
generation from Northcott, nonnegativity, the doubling lower bound, and only
one nontrivial translation estimate, namely translation by the fixed point
`T`.  It also removes that coordinate estimate by summing the base height
over the four translates by `T`.  Translation cyclically permutes the
summands, while doubling identifies opposite translates; a factor-four
duplication bound for the base height therefore gives a factor-two bound for
the symmetrized height.  Since `1 < 2`, Mathlib's descent theorem applies
directly.  The same file converts the concrete `TwoCosetExhaustion` witness
to the required sumset cover.
`X017RankZero.lean` instantiates this with the proved rational projective
`x`-height Northcott and duplication theorems.  It obtains finite generation
and combines `|E(ℚ)/2E(ℚ)| ≤ 2` with `|E(ℚ)[2]| = 2` to prove free rank
zero.  These theorems depend only on Lean's standard quotient/classical
axioms.
`X017FourTorsion.lean` proves the exact algebraic endgame conditional on the
uniform exponent-four statement.  If `2P=K=(0,0)`, the duplication identity
gives `x(P)^2=289`; the negative root is impossible on the curve, and the
positive root gives `P=T` or `P=-T`.  Combining this with the proved
two-torsion classification shows that any point killed by four is exactly
one of `0,K,T,-T`.  The needed two-adic good-reduction/formal-kernel proof is
supplied by the next two layers.
`X017FormalTwoCore.lean` supplies the first half of that input on the good
integral model.  It proves exact rational duplication formulas, shows that
every rational point is either two-integral or has formal valuations
`v₂(x)=-2k`, `v₂(y)=-3k`, and proves that doubling a nonzero formal point
raises `k` by at least one.
`X017FormalTwoReduction.lean` supplies the finite mod-two residue layer.
Every integral point enters the formal kernel after at most two doublings, so
`4P` is formal for every rational point.  Strict level growth gives the
separatedness statement that a formal point divisible by every power of two
through formal points must vanish.
`X017RationalPoints.lean` combines this separatedness with the exact
`{0,T}` cover.  Four times every point is divisible by every power of two,
so `4P=0`; the four-torsion classification then gives exactly
`0,K,T,-T`.  It further proves that the full point group is generated by the
order-four point `T` and has natural-number cardinality four.  All of these
declarations audit to Lean's standard quotient/classical axioms only.
`TateOrder17Quotient.lean` turns that rational-point classification into the
final order-17 exclusion.  It proves the needed normalized factor
nonvanishing, maps every hypothetical `F17=0` solution to the concrete
genus-one model, and eliminates all classified fibres by exact polynomial
identities and small modular or square-class contradictions.
`X017Reduction.lean` proves by kernel-checked finite computation that the
integral `X₀(17)` equation has three affine points over each of `𝔽₂` and
`𝔽₃`; with the point at infinity, both good fibres have four points.  It also
checks the discriminant factor is nonzero at both primes.  This reduction
route was not needed in the final proof, which instead uses the exact
two-coset descent and formal-kernel argument above.

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
  `s(reducedPoint, specialAnchor)`.
- `N13FiniteAffinePointInfinityClosure.lean` closes the finite degree-one
  special branch.  It identifies the abstract contracted infinity closure
  with the explicit weighted ideal `(1-at, v-bt³)`.  The proof shows that
  this ideal is already `t`-saturated because `a` is the inverse of `t`
  modulo the ideal; no primality or principality assumption is used.
  Reduction then gives `⊤` when `ā=0` and `(t-1,v-b̄)` when `ā=1`, exactly
  the two canonical point-chart cases.  After tensoring once with positive
  infinity, both reduced chart ideals equal those of
  `s(reducedPoint, specialAnchor)`.  Thus the special-fibre realization of
  every degree-one point line is complete.
- `N13SplitQuadraticSpecialRestriction.lean` packages proper reduction of an
  arbitrary two-adic affine point behind the same valuation case split as
  `pointLine`.  Its two chart ideals reduce to the canonical point pair.
  Tensoring proves literal affine- and infinity-chart equalities for every
  split secant divisor and every repeated-root tangent divisor.  It also
  returns a proper line and explicit special divisor whose generic affine
  ideal is the original quadratic Mumford graph.
- `N13EscapingPointPicardRealization.lean` closes the complete two-fibre
  `Data` package for an escaping degree-one point.  Tensoring with the
  positive-infinity anchor leaves the generic affine ideal unchanged.  The
  associated affine `pointMumford` has `nInf = 0`, so the oriented exponent is
  definitionally `-1`; the resulting `genericRaw` is literally
  `mumfordRaw`, and the generic Picard class is exactly `classOf`.  No
  geometric orientation theorem remains in this branch.
- `N13IntegralPointPicardRealization.lean` proves the identical oriented
  comparison for an integral affine point.  Its anchored finite closure has
  the standard generic point ideal, the same exponent `-1`, and the canonical
  divisor `s(reducedPoint, specialAnchor)` on both special charts.  Hence the
  complete degree-one two-fibre `Data` layer is now closed for both valuation
  regimes.
- `N13TwoChartPicardRealization.lean` now contains the generic bridge shared
  by every proper line: exact equality of the mapped affine ideal with a
  Mumford ideal gives equality of fractional-ideal units, literal
  `genericRaw = mumfordRaw` at exponent `nInf - 1`, and equality of oriented
  Picard classes.
- `N13SplitQuadraticPicardRealization.lean` applies that bridge to the
  split-specialization constructors.  Every distinct-root secant and every
  repeated-root tangent now yields complete two-fibre `Data`, with a literal
  special divisor and the exact original generic Mumford class.  At this
  historical stage the irreducible quadratic branch was the remaining
  degree-two Picard realization; the later finite and reciprocal producers
  below close it.
- `N13SpecialGraphDivisorCharts.lean` identifies the affine chart ideal of
  every quadratic special-fibre Mumford graph with the canonical chart ideal
  of its literal root divisor.  The distinct-root case is the graph-ideal
  Chinese remainder theorem.  The repeated-root case is now proved directly
  in characteristic two from `h(a) = 1`, so multiplicity is retained without
  a finite divisor table.  The same file computes the canonical infinity
  ideal as the product of the two root-point contributions.  Thus both
  target chart ideals of a horizontal special graph are explicit.  It does
  not by itself treat a reciprocal graph whose affine degree drops after
  reduction or handle the general vertical `{1,y}` relation.
- `N13SpecialInfinityGraphDivisor.lean` handles precisely the reciprocal
  degree-drop case on the special infinity chart.  A monic quadratic
  semigraph there still splits over `F₂`; roots at `t=0` are completed as
  points at infinity, while the nonzero root `t=1` is transported to the
  affine overlap.  `N13SpecialInfinityGraphDivisorCharts.lean` proves that
  this root divisor has the original quadratic infinity graph ideal,
  including the repeated-root tangent case, and computes its affine ideal
  as the product of the surviving `x=1` point contributions.
- `N13IntegralInfinityGraphSpecialRestriction.lean` closes the horizontal
  reciprocal specialization seam.  For every integral infinity semigraph
  with monic quadratic `u`, `deg v ≤ 3`, and `deg w ≤ 4`, coefficient
  reduction of its weighted two-chart line is literally the canonical chart
  pair of the completed special root divisor.  The affine proof classifies
  the four root patterns `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)` and preserves
  the doubled point in the last case.  No finite divisor table or additional
  geometric provider is used.
- `N13ReciprocalGraphPicardRealization.lean` feeds that exact chart-pair
  equality back into the irreducible reciprocal-horizontal recovery branch.
  Every `ReciprocalGraphClosure` now produces complete two-fibre `Data` whose
  generic raw ideal and oriented Picard class are the original quadratic
  Mumford representative.  At this stage the remaining irreducible
  realization work was confined to the finite contraction branches and the
  reciprocal vertical branch; both are closed by the later producers below.
- `N13SpecialVerticalDivisorCharts.lean` supplies the complementary literal
  chart calculation for the canonical `{1,y}` special fibres.  The two
  affine sheet ideals above `x=a` multiply to `(X-a)`.  Their infinity ideal
  is `⊤` above `x=0` and `(t-1)` above `x=1`.  Both identities are derived
  from the generalized graph-conjugation theorem, not from an ideal table.
  The same calculation now treats the base point at infinity uniformly:
  the canonical divisor over a constant infinity coordinate `t=a` has
  affine ideal `⊤` at `a=0`, affine ideal `(x-1)` at `a=1`, and infinity
  ideal `(t-a)` in both cases.
- `N13SpecialConstantInfinityVerticalGraph.lean` proves that a monic
  quadratic vertical graph with constant relation `t=a` is forced by the
  special curve equation to have ordinate polynomial `v²+v`; its graph
  ideal is therefore exactly `(t-a)`.
- `N13SpecialAffineSaturation.lean` proves the special-chart contraction
  principle used to avoid recomputing weighted affine closures.  If `x` is
  already a unit modulo an affine ideal, localization at the overlap loses
  no information.  Hence two compatible chart pairs with the same infinity
  ideal and `x`-saturated affine ideals are equal.  The property is also
  proved for the unit ideal and preserved by ideal products, so canonical
  completed-root divisors satisfy it root by root.
- `N13SpecialNonconstantInfinityVerticalGraph.lean` closes the remaining
  special vertical geometry.  In characteristic two the relation
  `t=a+v` is involutive, and the vertical ideal `(m(v),t-a-v)` is proved
  equal to the horizontal graph ideal `(m(t+a),v-t-a)`.  The translated
  polynomial remains monic quadratic and satisfies the required special
  infinity semigraph equation.
- `N13IntegralInfinityVerticalGraphSpecialRestriction.lean` applies these
  facts to both reciprocal vertical branches.  At `c̄=0` the whole reduced
  two-chart line is the canonical constant base fibre.  At `c̄=1` it is the
  completed divisor of the translated horizontal graph.  Since every
  element of `F₂` is zero or one, every integral vertical graph line now
  reduces to the canonical chart pair of a literal effective degree-two
  divisor.
- `N13ReciprocalVerticalGraphPicardRealization.lean` packages the exact
  vertical chart comparison with the contraction theorem for the generic
  ideal.  Combined with `N13ReciprocalGraphPicardRealization.lean`, the
  entire direct reciprocal-kernel branch now produces complete two-fibre
  Picard data, independently of whether rank-two recovery chooses the
  horizontal basis `{1,t}` or the vertical basis `{1,v}`.
- `N13SpecialInfinitySaturation.lean` supplies the dual contraction principle
  on the infinity chart.  If `t` is a unit modulo both infinity ideals, equal
  affine ideals and overlap compatibility force equality of the complete
  chart pairs.  The property survives reduction and is proved for every
  special graph or canonical fibre divisor used below.
- `N13SpecialQuadraticGraphRegularity.lean` proves that the special curve
  coefficient `1+X²+X³` is irreducible over `F₂`.  Hence every monic
  quadratic special graph is automatically regular, its reduced semigraph
  retains degree two, and its affine Mumford ideal is the canonical root
  divisor ideal.
- `N13SpecialAffineVerticalGraph.lean` computes both finite vertical-basis
  cases.  Slope zero is the canonical two-sheet fibre `(x-a)`; slope one is
  carried by the characteristic-two involution `y=x+a` to a regular
  horizontal quadratic graph, with equality of the corresponding affine
  ideals.
- `N13FiniteQuadraticSpecialRestriction.lean` closes the finite irreducible
  contraction branch.  The reflected monic relation makes `t` invertible
  modulo the source infinity closure.  The `{1,x}` basis gives a horizontal
  graph; the `{1,y}` basis gives one of the two vertical cases.  In all three
  cases infinity saturation upgrades the affine computation to exact
  equality with the canonical two-chart ideals of a literal effective
  divisor.
- `N13QuadraticPicardRealization.lean` is the complete degree-two capstone.
  It dispatches split secants, repeated-root tangents, finite irreducible
  contractions, and reciprocal irreducible horizontal-or-vertical recovery.
  Every balanced quadratic Mumford representative therefore has complete
  two-fibre `Data`, with its exact generic raw ideal, standard oriented
  generic Picard class, and canonical special divisor chart pair.
- `N13InfinityPointPicardRealization.lean` supplies the two missing
  projective degree-zero cases.  Two positive infinity lines realize the
  identity class and the doubled special anchor, while the negative line
  tensored with the positive anchor realizes the oriented difference of the
  two infinity sheets.  Both cases retain literal special chart ideals.
- `N13RationalCurvePointPicardRealization.lean` now gives every rational
  projective curve point complete two-fibre data.  Affine points are sent to
  the good two-adic model and split into integral and escaping branches; the
  generic class is proved equal to the rational Abel--Jacobi class after
  base change, and the special class is exactly the anchored class of proper
  reduction.  Packaging these realizations as rational `SpreadLine`s makes
  the `abel_reduces` field automatic for any concrete relation-first
  classifier on those lines.  It is therefore no longer an independent N13
  provider.
- `N13RationalPicardSpreadExistence.lean` closes global spread existence for
  every rational oriented Picard class.  Normalize the class to balanced
  Mumford degree at most two: degree zero uses the positive-infinity line,
  degree one extracts its affine rational point and selects the integral or
  escaping proper closure, and degree two uses the complete quadratic
  realization.  In degrees zero and one the proper chart line and literal
  special divisor are retained while only the independent generic infinity
  orientation is reset.  The resulting `SpreadLine` stores the original
  rational class literally, so it witnesses `exists_spread` for any proposed
  reduction kernel.  The stronger `exactSpreadLine` choice also retains raw
  generic equality with the coefficient extension of the rational balanced
  normal form, including the infinity orientation.
- `N13RationalAbelChartBase.lean` identifies the rational lift of the
  nonspecial Abel-chart base.  In sextic coordinates its exact Mumford datum
  is `u=X²+X`, `v=2X+1`, `nInf=0`; `v=1` would select the wrong sheet over
  `x=-1`.  The tensor product of the two integral point lines gives an
  explicit spread whose stored special divisor is literally
  `specialBaseDivisor`, and the affine ideal of that divisor is proved equal
  to `N13SpecialQuotientBasis.specialIdeal` through the existing quadratic
  graph-divisor theorem.  Rational-to-two-adic normal-form compatibility also
  proves that the canonical translated representative is exactly
  `mapMumford (normalizedMumford (z + rationalBasePic))`.
- All public spread theorems named above pass scoped compilation, bypass
  scanning, and `#print axioms`; their only dependencies are `propext`,
  `Classical.choice`, and `Quot.sound`.
- The remaining N13 mathematical providers on the stronger classifier route
  are the `class_eq_iff` specialization/reflection theorem for the now-global
  rational spread lines and first-jet doubling compatibility for the canonical
  recovered representatives.  These two inputs imply separatedness of the
  resulting reduction kernel.
  Pointwise
  compatibility of rational Abel classes with reduction (`abel_reduces`) is
  now supplied by the explicit curve-point realizations.  In the current
  design, separatedness reduces to constructing
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
- The near-base producer is reduced below direct mapped-special equality by
  `N13RationalPicardEndpoint.ExactSpreadAffineVerticallySaturated`, which is
  now proved by the certified exact-spread chooser.  Its assertion is that the
  affine lattice of each exact normalized spread has no
  component or scalar twist supported purely over the closed two-adic fibre.
  `exactSpreadLine_genericRaw` gives equality after vertical localization,
  and the existing contraction-uniqueness theorem upgrades it to literal
  equality with the canonical contraction.  This derived comparison does not
  mention the selected special ideal.  Given `class_eq_iff`, the translated
  spread then has the same special Abel class as the explicit base spread;
  regularity makes its stored divisor literal, and the base calculation
  derives the fixed special ideal.  This constructs
  `CanonicalMappedSpecialFamily` and lets `exists_diskPair_class_eq` supply
  the centered disk pair automatically.
- The representative choice can now be removed entirely: use the canonical
  balanced normal form `normalize (z + basePic)`.  A
  `CanonicalMappedSpecialFamily` stores only the literal mapped-special
  equality for those normal forms.  It recovers the centered disk pairs and
  reaches separatedness once the single family-level
  `FirstJetDoublingCompatibility` statement is supplied.
- Earlier axiom inventories in this file describe historical snapshots and
  must not be treated as current.  Use a fresh `#print axioms` audit of the
  assembled theorem before reporting the remaining global Mazur boundary.
- The source audit recovered as Q3802 confirmed that the broad N13 tail was
  already present: the 19-element special Abel set, selected quotient basis,
  integral graph/disk-pair recovery, relation-first classifier, reduction
  injectivity from `NSeparated`, transition-square estimate, and final
  rational-point-to-cusp implication are all proved.  Its then-missing
  irreducible quadratic special restriction is now closed by
  `N13FiniteQuadraticSpecialRestriction.lean` together with the reciprocal
  producers.  The pointwise two-fibre construction now removes
  `abel_reduces` from that list, and balanced Mumford exhaustion now removes
  global spread existence.  Vertical saturation is now carried from every
  direct constructor through the quadratic and rational degree-exhaustion
  choices into `exactSpreadLine`; the contraction comparison is consequently
  a theorem.  The genuine remaining producers are only `class_eq_iff` and the
  first-jet comparison for doubling.  No additional finite Jacobian group law
  or cardinality computation belongs on the critical path.
- `N13InfinitySpecialPointClass.specialPointClass_injective` proves that the
  anchored special Abel map loses no special curve point.  Away from the
  canonical pencil, equality of Abel classes gives equality of effective
  divisors.  In the canonical pencil, a divisor containing the fixed
  positive-infinity anchor is forced to be the infinity fibre, so its other
  point is negative infinity.
- This injectivity corrects the earlier interpretation of Q3805.  The
  pointwise reflection statement is logically sufficient for the endpoint,
  but `N13RationalPicardEndpoint.pointwiseReflection_iff_reduceCurve_injective`
  proves that it is exactly injectivity of proper reduction on rational curve
  points: rational Abel--Jacobi and anchored special Abel are both already
  injective.  Since the six rational cusps reduce bijectively to all six
  special points, this pointwise route is essentially the desired rational
  point classification itself, not a constructive shortcut to it.
- `N13RationalPicardEndpoint.lean` records the exact constructive endpoint.
  Global spread existence, pointwise Abel compatibility, and vertical
  saturation of each exact normalized spread are consumed automatically.
  The remaining providers are (1) `class_eq_iff` for the concrete rational
  spread lines and (2) first-jet compatibility comparing the chosen
  representative of `2z` with the square transition for `z`.  Saturation is
  strictly below both the contraction comparison and the former literal
  mapped-special field: both are now derived outputs.  The existing-first
  audit Q3893 found no supplier for the second remaining provider; its
  smallest honest form is the canonical Mumford
  `u`-deviation doubling congruence modulo the moving coordinate ideal square,
  which is equivalent to coordinate doubling rather than a weaker shortcut.
  These inputs produce two-adic separatedness and hence the primitive affine
  cuspidality theorem.  The assembly and the pointwise equivalence both
  compile and depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `N13QuotientVerticalFlatness.lean` and
  `N13TwoChartPicardRealization.lean` now identify affine vertical saturation
  exactly with relative torsion-freeness of the quotient over `ℤ₂` and
  expose three reusable sufficient forms: canonical contraction, unit ideal,
  and monic integral Mumford graph.  The actual spread constructors supply
  this property for the two infinity cases, integral affine points, finite
  quadratic contractions, and the horizontal and vertical reciprocal graph
  branches.  The primitive nonmonic escaping graph
  `(1-t₀X, Y-v₀X³)` is also saturated: its monic infinity point ideal is
  saturated, localization preserves that property, and the generator
  `1-t₀X` supplies the `XUnitMod` witness needed to contract back exactly.
  Thus invertibility is no longer being conflated with flatness: each covered
  branch has a separate saturation certificate.
- `N13QuadraticTwoChartSpreadSaturation.lean` closes the product case.  If
  two integral ideals are vertically saturated and the first is invertible
  in the common function field, multiplying by its inverse fractional ideal
  reduces scalar cancellation in their product to cancellation in the second
  ideal.  This proves that tensoring saturated two-chart lines preserves
  saturation, hence certifies `pairLine` for both split secants and coincident
  repeated-root tangents.  The strengthened split, repeated, reciprocal,
  quadratic, rational degree-zero/one/two, and exact-spread existentials retain
  these certificates.  The selected exact spread exposes saturation directly,
  so this branch is closed without localization reflection or a new axiom.
- `N13MumfordCenteredDoublingJet.lean` gives a denominator-free local
  calculation for the remaining first-jet producer.  It expands the centered
  Mumford square, proves the exact linearized double and the Hensel ordinate
  error, and shows that coefficients one and three of
  `P.u² - uBase * Q.u` modulo the moving ideal square force literal doubling
  of both disk coordinates.  `N13MumfordCenteredDoublingAdapter.lean` then
  subtracts the already proved transition-square estimate and constructs the
  existing `FirstJetDoublingCompatibility` package.  Thus the genuine
  arithmetic residue is precisely those two cross-coefficient memberships
  for the canonical recovered representatives of `z` and `2z`; no Picard
  classification, separatedness, or additional coordinate comparison is
  hidden in the reducer.  The three terminal declarations audit to Lean's
  standard quotient/classical axioms only.
- `recoveredPair_mumford_eq_centeredDouble` now identifies the canonical
  representative at `2z` with the centered double in the transported
  Mumford group.  This is useful wiring, but the group law itself is defined
  through canonical normal forms, so the equality does not definitionally
  expose the coefficients of the doubled `u`-polynomial.  The remaining N13
  arithmetic task is still to prove that coefficients one and three of
  `P.u² - uBase * Q.u` lie in the square of the source coordinate ideal; it
  cannot be weakened to the square of a larger joint ideal.

### N25 shared Frobenius descent and the binary class-number consumer (2026-08-10)

- The characteristic-two executable tables are now connected to honest
  semantic fields.  `BinaryFieldModel` installs the certified table laws as
  field structures on wrapper carriers, and explicit chart equivalences prove
  that the raw predicates are exactly the field-valued quadric-cubic
  equations.  This is a semantic equation bridge, not an equivalence inferred
  from equal point counts.
- `FiniteFieldFrobeniusDescent.lean` now owns the prime-generic common-field
  construction.  A `Realization` bundles the chosen embedding with the
  equivalence onto the `p^d`-power-fixed subtype and records their pointwise
  coherence.  Normalized-projective descent therefore cannot accidentally
  combine two unrelated noncomputable embedding choices.
- `NormalizedProjectiveCurveFrobenius.lean` restricts projective descent to a
  `CurveModel` whose sole geometric law is preservation and reflection under
  coefficient homomorphisms.  The characteristic-two and characteristic-three
  canonical equations are thin adapters to this shared layer.  The former
  500-line characteristic-three finite-field/descent duplication has been
  replaced by compatibility wrappers around the generic construction.
- The semantic binary point counts `5,5,20,29` are now realized as fixed points
  of arithmetic Frobenius on the common field `𝔽_(2^12)`.  Exact-period
  orbits produce an honest closed-point grading through degree four.  The
  marked-divisor recurrence gives `A₂=15` and `A₄=101`; the already proved
  middle Riemann--Roch counting identity then gives `#Pic⁰=71` from the actual
  degree-two/degree-four Picard fibre and rank identities.
- This closes the characteristic-two field-semantics and Frobenius-orbit seam,
  but it does not yet construct the geometric Picard group or prove
  Riemann--Roch for the explicit smooth proper fibre.  The honest next N25
  provider is the local divisor/principal-divisor/Picard realization supplying
  the degree-two and degree-four complete-linear-system fibres and
  `l(D)=l(K-D)+1`.  Good-reduction maps, rational rank zero, pullback/norm, and
  the final Abel--Jacobi classification remain downstream.
- Real Lake builds of both characteristic-specific middle Riemann--Roch
  consumers pass.  Axiom audits of the generic projective descent, generic
  curve descent, the semantic `F16` count, both fixed-point realizations, and
  both final conditional class-number consumers contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

### N25 actual divisor-class quotient and binary hyperplane section (2026-08-10)

- `CurveDivisorPicard.lean` extends the closed-point grading to signed
  integer divisors and an integer degree homomorphism.  Given an actual
  principal-divisor subgroup and its degree-zero theorem, divisor degree now
  descends to the quotient and `Pic^n` is defined as its literal degree fibre.
- Effective divisors map to these quotient fibres with their degrees proved.
  Translation by a degree-one class gives `Pic^n ≃ Pic^0`; a degree-six class
  gives the genus-four residual equivalence `Pic^4 ≃ Pic^2` by `D ↦ K-D`.
  The middle Riemann--Roch consumers for both residue characteristics now have
  specializations to this one quotient, so unrelated finite proxy types can
  no longer masquerade as the three Picard degrees.
- A computable normal-form map is accepted only after proving that its kernel
  is exactly the principal subgroup and that it is surjective.  Those two
  structural certificates produce an additive equivalence from the quotient;
  its finite cardinality is then a consequence rather than an input.
- In characteristic two, the hyperplane `x=0` makes the canonical cubic
  factor as `z*w*(y+z+w)`.  Exact restriction identities for the quadric give
  the multiplicity pattern
  `2[0:0:0:1] + [0:0:1:0] + 3[0:1:1:0]`.
  All three points are realized as degree-one Frobenius closed points, and the
  displayed effective divisor is proved to have degree six.
- `RationalPointsN25QuotientTwoHyperplaneArtin.lean` now proves the
  scheme-local algebra behind the two nonreduced multiplicities.  On
  `D(y+z+1)` the `w=1` chart ideal is exactly `(y^2,z)`; on `D(1+b)` the
  translated `y=1` chart ideal is exactly `(a+b+a*b,b^3)`.  The file constructs
  the length-two and length-three Artin targets `F_2[t]/(t^2)` and
  `F_2[t]/(t^3)`, proves their dimensions, and gives surjective affine-plane
  evaluations killing both chart equations.  Since both denominators map to
  `1+t`, the evaluations are extended through the corresponding
  `Localization.Away` rings.
- `RationalPointsN25QuotientTwoHyperplaneArtinKernel.lean` closes both
  reverse kernel containments by explicit algebra equivalences
  `F_2[y,z]/(y^2,z) ≃ F_2[t]/(t^2)` and
  `F_2[a,b]/(a+b+a*b,b^3) ≃ F_2[t]/(t^3)`.  At the tripled point the proof
  derives `a=b+b^2` by using `b^3=0` to make `1+b` a unit; it does not infer
  injectivity from equal dimensions.
- `RationalPointsN25QuotientTwoHyperplaneArtinLocal.lean` closes the
  principal-open packaging.  A reusable `awayLift_ker` lemma specializes
  Mathlib's theorem that localization commutes with kernels.  On each open it
  proves that the ideal generated by the actual curve equations is exactly
  the kernel of the localized Artin evaluation.  Hence the local quotient
  rings, not merely their point sets or dimensions, have the asserted
  length-two and length-three presentations.  The multiplicities are no
  longer supported only by set-theoretic factorization.
- `RationalPointsN25QuotientTwoConormal.lean` starts the adjunction layer at
  the strongest level supported by the current Mathlib API.  It realizes the
  binary canonical affine cone as
  `F_2[x,y,z,w]/(Q,C)`, proves evaluation compatibility with the stored
  coordinate equations, proves that `Q` and `C` are homogeneous of degrees
  two and three, computes `dQ` and `dC` in the free basis
  `dx,dy,dz,dw`, and identifies those evaluated rows with the Jacobian rows
  used by the geometric smoothness certificates.  Mathlib's general theorem
  then supplies the concrete exact conormal sequence and the surjection onto
  the quotient's Kähler differentials.
- `RationalPointsN25QuotientTwoRegularSequence.lean` proves structurally that
  the same `(Q,C)` is a regular sequence.  It separates `y`, identifies the
  quadric quotient with the free quadratic algebra
  `F_2[x,z,w][y]/(y^2+zy+xz+xw+zw)`, and computes the two-by-two matrix of
  multiplication by the cubic.  Its determinant is nonzero by evaluation at
  `(x,z,w)=(0,1,1)`, so the cubic is not a zero divisor modulo the quadric.
  An explicit polynomial-tower and quotient equivalence transports this
  statement back to `F_2[x,y,z,w]`; the final theorem is Mathlib's actual
  `RingTheory.Sequence.IsRegular`, not a dimension heuristic or an assumed
  complete-intersection label.  This closes the algebraic complete-
  intersection premise of adjunction.
- `RationalPointsN25QuotientTwoKoszul.lean` turns that regularity theorem into
  the explicit exact sequence
  `0 → R → R² → R → R/(Q,C) → 0`.  The two maps are
  `r ↦ (Cr,-Qr)` and `(a,b) ↦ Qa+Cb`; the proof classifies an arbitrary
  syzygy using the proved non-zero-divisor property of `C` modulo `(Q)` and
  identifies the middle range with the literal ideal `(Q,C)`.  This closes
  the ungraded Koszul-exactness premise without coefficient enumeration.
- `RationalPointsN25QuotientTwoConormalBasis.lean` now proves the actual
  complete-intersection conormal module formula at the affine-cone level:
  the classes of `Q` and `C` induce an `S/(Q,C)`-linear equivalence
  `(S/(Q,C))² ≃ I/I²`, hence concrete finite and free instances.  For
  injectivity, a relation modulo `I²` is corrected by coefficients already
  in `I`; the residual relation is then forced by the proved Koszul
  exactness to be `(Cr,-Qr)`.  Thus the two conormal generators are genuinely
  independent over the quotient, rather than merely a chosen generating
  pair.  This is the algebraic source of the future graded formula
  `I/I² ≅ O_C(-2) ⊕ O_C(-3)`.
- `RationalPointsN25QuotientTwoConormalGrading.lean` preserves the degrees
  discarded by that ungraded equivalence.  Its degree-`n` coefficient piece
  is `B_{n-2} × B_{n-3}`, with the missing negative degrees represented by
  zero submodules, and its image in `I/I²` is stable under homogeneous scalar
  multiplication.  The defining quadric and cubic classes are proved to lie
  in conormal degrees two and three.  Mathlib constructs the direct ground-
  field and quotient-ring actions on `I/I²` through different quotient
  paths; the file proves their compatibility on cotangent representatives
  rather than installing an unjustified global scalar-tower instance.  An
  explicit reindexing of the quotient decomposition shifts the two coefficient
  families by two and three, zips them degreewise, and transports them through
  the conormal equivalence.  The inverse is proved to be literal recomposition,
  so the pieces form an internal direct sum and supply a
  `DirectSum.Decomposition` of `I/I²`.  Mathlib's standard
  `GradedModule.linearEquiv` then packages these data as a genuine `B`-linear
  equivalence from `I/I²` to the external direct sum of its homogeneous
  pieces; its underlying maps are definitionally the explicit decomposition
  and recomposition maps.  Each shifted coefficient family is itself now a
  graded `B`-module with a canonical decomposition, yielding the direct
  `B`-linear formula `I/I² ≃ B(-2) ⊕ B(-3)` in the external direct-sum model.
- `FLT/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/TwistingTransition.lean`
  begins the missing projective twisting API at its algebraic core.  For any
  two degree-one homogeneous chart equations `f,g`, it constructs the overlap
  unit `g/f` inside Mathlib's degree-zero homogeneous localization, proves its
  explicit inverse `f/g`, and packages multiplication by `(g/f)^d` as the
  transition equivalence for a negative twist.  The three ratios on an
  ordered triple overlap satisfy `(g/f)(h/g)=h/f` by a kernel-checked
  localization calculation.  Explicit `awayMap` restrictions from each
  pair overlap to the same ordered triple overlap are constructed and proved
  to send the pairwise ratios to those representatives, so this is now an
  actual Čech cocycle rather than three unrelated equalities in a convenient
  ring.  The N25 specialization proves that all four
  quotient coordinate classes have degree one and instantiates these units,
  twist transitions, and cocycles on its standard projective charts.  The
  transition arithmetic also proves that the determinant of the conormal
  shifts has debt `2+3=5` and that combining its dual with the ambient
  canonical debt four gives precisely the positive twist by one, chart by
  chart.
- `RationalPointsN25QuotientTwoGradedKoszul.lean` defines
  `shiftedPiece debt n = S(-debt)_n`, proves that multiplication by a
  degree-`d` polynomial maps `S(-(e+d))_n` into `S(-e)_n`, and constructs the
  shifted Koszul maps in every degree.  A structural homogeneous-component
  cancellation lemma forces each ungraded syzygy witness to have degree
  `n-5`, including the low-degree zero cases.  Consequently the full
  degreewise sequence is exact and its right projection is surjective.
- `RationalPointsN25QuotientTwoQuotientGrading.lean` proves that `(Q,C)` is
  homogeneous and identifies the presented cokernel in every degree with the
  literal image of the corresponding homogeneous polynomials in `S/(Q,C)`.
  The kernel computation takes homogeneous components of an arbitrary ideal
  representation, so it is structural rather than a dimension comparison.
- `RationalPointsN25QuotientTwoGradedAlgebra.lean` maps the standard polynomial
  decomposition componentwise into those literal pieces and proves that its
  kernel is the kernel of the quotient map.  Hence canonical recomposition is
  bijective.  Together with multiplication of homogeneous representatives,
  this gives the quotient its actual internal `GradedAlgebra` structure and a
  surjective graded quotient map, with explicit formulas for every projection.
- `RationalPointsN25QuotientTwoProj.lean` proves the irrelevant-ideal
  hypothesis for that graded quotient map and constructs the actual
  projective quotient and its canonical morphism to binary projective
  three-space.  Standard projective basic opens pull back to the corresponding
  quotient basic opens.  A structural degree-zero argument shows that the
  Koszul source vanishes there and every degree-zero homogeneous polynomial is
  constant, yielding `literalConePiece 0 ≃+* F_2` and the structure morphism
  to `Spec F_2`.
- `FLT/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/ClosedImmersion.lean`
  proves structurally that a surjective graded map remains surjective after
  homogeneous localization and hence induces a closed immersion on `Proj`.
  `RationalPointsN25QuotientTwoClosedImmersion.lean` applies this theorem to
  the canonical quotient, so the constructed projective scheme is now an
  actual closed subscheme of binary projective three-space.
- `RationalPointsN25QuotientTwoProper.lean` proves finite generation first
  over `F_2` and then over the degree-zero quotient piece.  Mathlib's projective
  properness theorem and the degree-zero ring equivalence therefore show that
  the canonical structure morphism to `Spec F_2` is proper.
- `RationalPointsN25QuotientTwoChartIdeal.lean` identifies the affine equations
  of that closed immersion on every standard projective chart.  It first
  proves that `Q/X_i^2` and `C/X_i^3` vanish, then lifts an arbitrary kernel
  fraction to a homogeneous numerator.  Localization vanishing supplies a
  power `X_i^m`; degreewise Koszul exactness expresses
  `X_i^m p = Qa+Cb`.  Regrading `a` and `b` as degree-zero fractions and
  cancelling the inverted coordinate proves the exact structural formula
  `ker(Away(S,X_i) → Away(S/(Q,C),X_i)) = (Q/X_i^2,C/X_i^3)`.
  Surjectivity of homogeneous localization and the first isomorphism theorem
  then package the target chart ring as the quotient by this explicit ideal,
  with the equivalence induced pointwise by the canonical chart map.  Thus
  the localized defining ideal and affine quotient rings are no longer open
  premises; they provide the local input for the global ideal-sheaf
  comparison below.
- `RationalPointsN25QuotientTwoChartKoszul.lean` constructs the complete
  affine Koszul complex on every ambient standard chart.  Its differentials
  are multiplication by the actual degree-zero equations
  `Q/X_i^2` and `C/X_i^3`, and its cokernel is the explicit curve-chart
  quotient.  Exactness at the middle free module is proved uniformly, not by
  expanding four affine polynomial systems: two arbitrary homogeneous
  fractions are put over a common power of `X_i`, the remaining denominator
  is cancelled in the ambient polynomial domain, and degreewise Koszul
  exactness supplies a homogeneous witness of exactly the degree needed to
  descend back to the chart.  This closes the algebraic exactness on the
  standard affine cover.
- `FLT/Mathlib/AlgebraicGeometry/Modules/TildeExact.lean` proves the missing
  reusable categorical theorem that affine tilde preserves exact short
  complexes.  The proof forgets to abelian-group sheaves, checks exactness on
  stalks, identifies the actual stalk map of `tilde.map` with the canonical
  localized linear map by germ naturality and denominator cancellation, and
  invokes exactness of module localization.  It does not assume an unproved
  quasi-coherent-sheaf exactness API.
- `RationalPointsN25QuotientTwoChartKoszulSheaf.lean` packages the two
  overlapping three-term pieces of the four-term chart Koszul resolution and
  applies this theorem.  Hence the actual affine-tilde module-sheaf morphisms
  are exact on every one of the four ambient standard charts.  The remaining
  categorical step is global: compare these local free sheaves and arrows with
  the effective projective twists, prove overlap compatibility, and glue the
  ambient Koszul resolution on projective three-space.
- `RationalPointsN25QuotientTwoIdealSheaf.lean` closes that gluing seam against
  Mathlib's actual global object.  Functoriality of `Proj` identifies the
  section map on `D_+(X_i)` with the localized graded quotient, while the
  target `Away`-to-sections map is injective because it is an isomorphism.
  Consequently, pulling back the restriction of
  `canonicalProjectiveCurveMap.ker` along
  `Away(S,X_i) ≃ Γ(D_+(X_i),O)` gives exactly
  `(Q/X_i^2,C/X_i^3)` on all four standard charts.  The local ideals are now
  proved to be restrictions of the single global kernel ideal sheaf rather
  than a parallel chartwise construction.
- `RationalPointsN25QuotientTwoAffineChart.lean` supplies the missing ordinary
  coordinates on `D_+(X_0)`.  The three-variable polynomial ring maps each
  affine variable to `X_{j+1}/X_0`; setting `X_0=1` gives its inverse.  The
  proof that every homogeneous fraction lies in the image invokes
  `Away.adjoin_mk_prod_pow_eq_top` and proves the required monomial identity
  from total degree, so it is independent of coefficient enumeration.  The
  equivalence sends the displayed affine quadric and cubic exactly to
  `Q/X_0^2` and `C/X_0^3`, yielding the literal ordinary quotient presentation
  of the first N25 projective chart.
- `FLT/Mathlib/RingTheory/RingHom/SmoothJacobian.lean` adds the structural
  Mathlib-facing bridge for a finite family of selected presentations.  A
  selected Jacobian becomes a unit after localizing at itself, and Jacobians
  spanning the unit ideal therefore imply smoothness by target-localization
  locality.  This theorem is independent of the N25 equations.
- `RationalPointsN25QuotientTwoAffineSmooth.lean` applies that bridge to the
  first chart.  Euler homogeneity rewrites the two projective minors involving
  the removed `x` coordinate through the three affine minors.  Three naive
  two-relation presentations select the `(z,w)`, `(y,w)`, and `(y,z)` minors;
  the resulting Bezout identity proves that their quotient Jacobians span the
  unit ideal.  Hence both the ordinary quotient presentation and the actual
  degree-zero coordinate ring of `D_+(X_0)` are smooth over `F_2`.  No finite-
  field enumeration or quotient-representative computation enters the proof.
- `RationalPointsN25QuotientTwoAffineCharts.lean` extends the coordinate
  package uniformly to every `D_+(X_i)`.  Its affine variables are literally
  indexed by `{j : Fin 4 // j ≠ i}`.  A monomial fraction is first written as
  the product of all four ratios `X_j/X_i`; the diagonal ratio is one and is
  erased structurally, so no chart permutations or coordinate case split are
  needed.  Uniform dehomogenization supplies the inverse.  The same
  equivalence carries the dehomogenized quadric-cubic ideal to the proved
  homogeneous chart ideal, giving an ordinary two-equation quotient
  presentation of all four actual projective charts.
- `RationalPointsN25QuotientTwoStructuralJacobian.lean` supplies the uniform
  derivative layer without chartwise expansion.  It proves by polynomial
  induction that setting `X_i=1` commutes with partial differentiation in
  every non-pivot coordinate.  Mathlib's homogeneous Euler identity then
  controls all ambient two-by-two Jacobian minors in the source ring
  `F_2[x,y,z,w]`.  Naturality lemmas carry the coordinate equations, gradient
  minors, and the four stored Bezout certificates through arbitrary ring
  homomorphisms.
- `RationalPointsN25QuotientTwoAffineChartsSmooth.lean` applies that layer to
  all four ordinary chart quotients.  Three selected two-relation
  presentations give the three free-coordinate minors.  A finite lemma only
  identifies unordered coordinate-label pairs; Euler's identity removes the
  normalized pivot column.  The Bezout certificates are instantiated in the
  source polynomial ring and only then mapped to each quotient, so the proof
  neither expands derivatives chart by chart nor asks the possibly zero
  quotient ring for a `CharP 2` instance.  The three presentation Jacobians
  span the unit ideal on every chart, and smoothness transports through the
  proved equivalences to all four actual degree-zero projective chart rings.
- `RationalPointsN25QuotientTwoSmooth.lean` closes the scheme-level gluing
  step.  Every positive-degree homogeneous quotient class lifts to a
  homogeneous polynomial divisible monomial-by-monomial by some coordinate,
  so the four coordinate classes generate the quotient irrelevant ideal.
  Mathlib's `Proj` construction therefore supplies the corresponding four
  affine opens as an actual cover.  On each member, `awayι_toSpecZero`
  identifies the restricted structure morphism with the spectrum map of the
  coefficient homomorphism; uniqueness of a ring homomorphism out of
  `ZMod 2` matches this with the algebra map used by the affine Jacobian
  proof.  Source-Zariski locality then proves the projective structure
  morphism `canonicalProjectiveCurveToSpec` smooth.  The generic selected-
  Jacobian bridge also retains presentation dimension under localization:
  each chart has three affine variables and two relations.  Transport and
  gluing therefore strengthen the result to
  `SmoothOfRelativeDimension 1 canonicalProjectiveCurveToSpec`, so Mathlib
  now recognizes the constructed projective quotient as a smooth curve over
  `F₂`, not only as an unspecified-dimensional smooth scheme.
- `RationalPointsN25QuotientHilbert.lean` now connects the degreewise Koszul
  resolution to the actual internal grading at the level of dimensions.
  Each shifted homogeneous polynomial piece is finite-dimensional because
  only finitely many exponent vectors have a fixed total degree; the literal
  quotient piece is finite-dimensional through its proved cokernel
  equivalence.  Rank-nullity on the four-term exact sequence proves the exact
  alternating finrank identity for every degree.  A structural stars-and-bars
  argument then evaluates every shifted piece, proving that the literal
  quotient finrank equals the complete-intersection Hilbert-series coefficient
  in every degree and is `6n-3` above the degree-five numerator bound.  The
  only remaining Hilbert seam is now the scheme-theoretic comparison between
  this graded coordinate-ring Hilbert function and the `Proj` Hilbert
  polynomial.
- The remaining adjunction gap is now narrower: the conormal module is free
  on the actual equation classes, and its shifted degree pieces, homogeneous
  scalar action, generator degrees, internal direct sum, and canonical
  decomposition are explicit.  The remaining step is geometric: Mathlib still
  lacks the associated graded-module sheafification and projective
  twisting-sheaf determinant theorems needed to carry this decomposition to
  `Proj` and conclude `ω_C ≅ O_C(-4+2+3) = O_C(1)`.  The degree-one affine
  chart transition units and their cocycle are no longer part of that gap;
  the unit cocycle is proved uniformly for every integral power, so the same
  descent datum covers all `O(d)` occurring in adjunction.  Its Čech
  equalizer is now effective on the standard cover, so each resulting global
  twist restricts to the chosen free rank-one chart model.  The remaining
  gap is therefore the ambient sheafified Koszul/conormal sequence and its
  determinant comparison, not construction or local freeness of `O(d)`.
- `RationalPointsN25QuotientTwoTwistingSheafCharts.lean` lifts this descent
  datum into actual local sheaves of modules.  Each coordinate chart is the
  affine `Spec` of its homogeneous-away ring, and every integral twist is
  modeled there by the affine tilde sheaf of a free rank-one module.  Pair
  transitions and their restrictions to ordered triple overlaps are mapped
  through the tilde functor; functoriality upgrades the module cocycle to a
  categorical cocycle of local module-sheaf isomorphisms.  The subsequent
  gluing file constructs the global module sheaf and proves that its chart
  restrictions are the chosen free rank-one local models.  The remaining
  task is to promote the chartwise determinant/adjunction identity to a
  sheaf isomorphism.
- `RationalPointsN25QuotientTwoTwistingDescent.lean` connects those explicit
  affine overlaps to the categorical geometry required by descent.  The
  pullback of any two coordinate-chart maps is identified with the affine
  spectrum of the degree-zero localization away from `x_i x_j`; both
  pullback projections are proved to be the expected localization maps.  The
  same objects are packaged as Mathlib `ChosenPullback`s, and compatible
  threefold wide pullbacks are supplied from nested categorical pullbacks.
  `FLT/Mathlib/AlgebraicGeometry/Modules/PullbackUnit.lean` proves the generic
  missing comparison saying that the unit module sheaf pulls back along an
  open immersion to the unit sheaf.  It now also proves the affine-generator
  naturality of `tilde.toOpen` and the generic conjugation theorem saying that
  restriction sends multiplication by a unit to multiplication by its image.
  This transports each explicit affine transition to the exact pair-overlap
  morphism expected by Mathlib's 2026 `DescentData'` API.  The ratio transition
  on a self-overlap is proved structurally to be the identity, through the
  ring, unit, module, tilde, and categorical-overlap layers.  Completing
  `DescentData'` directly would still require substantial pseudofunctor unit
  and associativity bookkeeping; no stack-effectivity theorem for scheme
  modules has been found in the pinned Mathlib.
- `RationalPointsN25QuotientTwoTwistingSheafGluing.lean` avoids treating that
  bookkeeping as a new axiom.  It realizes the explicit affine pair overlaps
  as the actual intersections of chart open immersions, identifies both
  restricted local twist sheaves with the explicit free rank-one overlap
  sheaf, and inserts the proved coordinate-ratio transition between them.
  The three pair-to-triple localization maps are now explicit open
  immersions.  Restricting and conjugating each pair transition is proved to
  equal its corresponding triple transition, and these three equalities are
  combined with the algebraic ratio identity to give the actual Čech cocycle
  on every ordered triple intersection.  Thus the cocycle used by the gluing
  construction is no longer only a parallel calculation on affine rings.
  The standard Čech equalizer
  `Eq (∏ i, j_i* F_i ⇉ ∏ i j, j_ij* F_ij)` is then formed inside the category
  of module sheaves on the canonical projective curve.  The resulting
  `globalTwistModule d` is an honest global module sheaf and its pair-overlap
  compatibility is kernel-checked.  The sectionwise Beck--Chevalley and
  limit-preservation infrastructure in `PullbackUnit.lean` allows that
  equalizer to be restricted to a fixed chart.  The explicit reconstruction
  from one chart component is proved to satisfy every ordered-pair relation;
  conversely, an equalizing family is determined by that component.  These
  inverse maps give `coordinateLocalToRestrictedGlobalTwist_isIso` and the
  packaged isomorphisms `globalTwistModuleLocalIso` and
  `globalTwistModuleLocalUnitIso`.  Hence `globalTwistModule d` restricts to
  a free rank-one module sheaf on all four standard charts.  Twist
  effectivity and local freeness are closed without a new axiom; the next
  geometric work must connect the ambient Koszul/conormal morphisms to these
  effective twists.
- The characteristic-two terminal consumer now fixes its base class to
  `[0:0:0:1]` and its residual class to this explicit degree-six hyperplane
  section.  The remaining geometric seam is exact: construct principal
  divisors, formalize the projective adjunction step identifying the
  hyperplane section with the canonical class, construct the degree-two and
  degree-four complete-linear-system fibres, and prove the associated middle-
  degree Riemann--Roch ranks.
