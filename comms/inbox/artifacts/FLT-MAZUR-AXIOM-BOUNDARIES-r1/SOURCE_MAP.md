# FLT accepted-source map: three remaining custom axioms

## Current result

Authoritative accepted source: [22f88d43187caf0e57affcc6ded92cdf9b49714a](https://github.com/xiangyazi24/FLT/commit/22f88d43187caf0e57affcc6ded92cdf9b49714a).
Lead receipt: [r5 at dispatch 1222d33fa09e5a00d29c6ad294f3dfb32baf26ce](https://github.com/xiangyazi24/FLT/blob/1222d33fa09e5a00d29c6ad294f3dfb32baf26ce/comms/outbox/lead-FLT-N13-ENDPOINT-receipt-r5.md).
This receipt supersedes r4 and arrived before this delivery was published.

**N13 is integrated and discharged.** The lead reports:
- all 57 N13 modules compiled
- aggregate build of the 27 remaining modules plus TorsionBound completed successfully, 9,103 jobs
- all 137 public theorems in those 27 modules emit only `propext`, `Classical.choice`, and `Quot.sound`
- the N13 axiom was replaced by the exact constructed theorem; type identity checked with `example : type_of% @A := @B`
- the fresh `MazurProof.mazur_torsion_bound` audit has **no sorryAx** and exactly these three custom axioms:

```text
MazurProof.no_prime_order_ge_23
MazurProof.CyclicExclusion25.no_explicit_order25_obstruction
MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction
```

These are lead-reported fresh emitted results, not a dot emission or a deduction from import graphs. We separately read the current CyclicExclusion13 source and verified its theorem replacement and import. The full tree differs from its parent 62968808 in that one source file only.

The old four-axiom analysis at requested r4 pin `6aef0f8bdea96652f4879d0f74acd6bf189f306c` remains historically valid but is no longer the live boundary. `HISTORICAL_R4_SOURCE_MAP.md` and `N13_ACCEPTED_CHAIN.md` preserve that provenance; their former next-step wording is explicitly superseded. **Do not redo N13 wiring or ask for an aggregate already supplied by r5.**

Whole Mazur is not axiom-free: three genuine arithmetic boundaries remain.

## Source and emitted dependency distinction

At 22f88d4 the reconstructed repository-local source import closure has **539 files**, plus **202 external import paths**. Its files match the accepted pinned tree, using the earlier fully read and byte-hashed files where Git blobs are unchanged and the freshly read C13 replacement. All 539 current local files are backed by a matching recomputed Git blob, including that new replacement.

The local import closure has four literal custom axioms:
- the three emitted dependencies above
- imported legacy `MazurProof.mazur_prime_torsion_bound`

It also contains seven literal sorry tokens in old Kubert, scratch DischargeN14, and FLT/EllipticCurve/Torsion declarations. The lead's fresh root emission excludes both the legacy custom axiom and sorryAx. Their import presence is therefore not endpoint proof-term dependence.

The prior detailed source scans covered 213 baseline-root files at 6aef and 335 constructed-N13 files at 62968808. All 548 fetched source instances passed independent byte-level recomputation of their pinned Git blob SHA-1; source SHA-256 hashes are recorded. The current tree comparison establishes continuity for reused files. See `SOURCE_AUDIT.json`, `SOURCE_BLOB_VERIFICATION.json`, and `CURRENT_SOURCE_AUDIT.json`.

All 152 reviewed N25/N49-family Lean files have identical blobs between 6aef and accepted 22f88d4. Their exact statements, line numbers, geometric developments, and missing inputs below are unchanged. The separate full family review is `N25_N49_REVIEW.md`.

The lead records 383/384 public headers identical to the delivered version, with a basePair type ascription plus a public DiskPair.mumford alias, a private coefficient-map helper and ambiguity-hiding adjustments. These accepted changes are preserved as provenance, not described as byte-identical original delivery.

No dot Lean, lake, compilation, cache, runtime or kernel operation was run. Source metadata pins Lean v4.31.0-rc2 and Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Emitted results and build acceptance belong to the lead.

## Common active source route

The exact root is [TorsionBound.lean:51–76](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/TorsionBound.lean#L51-L76):

```lean
theorem mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionSet E).Finite ∧ (torsionSet E).ncard ≤ 16
```

The three branches meet at `MazurProof.mazur_cyclic_order_bound_assembled` (CyclicOrderAssembly:204), then `MazurProof.mazur_cyclic_order_bound` (Axioms:289). This reaches the root through:
1. private `n_in_mazur_list_of_structure` (TorsionBound:20), called at root line 59
2. private `torsionSet_subset_2520_torsion` (TorsionFiniteFromOrderBound:26) → `rational_torsion_finite` (line 41), called at root line 53

Private names are source labels, not asserted generated kernel-private identifiers.

## 1. N25: primitive order-25 Tate locus

FQN: `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`.
[Exact declaration, CyclicExclusion25.lean:47](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/CyclicExclusion25.lean#L47):

```lean
axiom no_explicit_order25_obstruction : ¬ ExplicitOrder25Obstruction
```

Expanding the aliases and F5 retains the exact proposition:

```lean
¬ ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic
      (MazurProof.TateOriginDivision.W b c),
      b ≠ 0 ∧ b - c ≠ 0 ∧
        MazurProof.TateOrder25Factor.F25 b c = 0
```

The Tate curve has coefficients (1-c,-b,-b,0,0), hence equation
`y²+(1-c)xy-by=x³-bx²`. F25 is the explicit degree-40 primitive factor after removal of the proper order-five factor, with
`preΨ′₂₅(0)=b²⁰⁸(b-c)F25(b,c)`.
Ellipticity and the nonzero factors are essential. This is exclusion of nonsingular exact-order-25 Tate data, not unrestricted polynomial nonvanishing.

Active users:
- direct `CyclicExclusion25.no_rational_point_of_order_25`, lines 49–54
- `MazurProof.no_order_25`, CyclicOrderAssembly:170
- private `no_order_bad_composite`, call at line 197
- common cyclic assembly/root route above

Equivalent tracked proof: **none found** in the complete N25/N49 family review. The actual Tate-to-genus-four-canonical-model map and source cusp avoidance are proved, but target rational-point exhaustion is not. Current source already has properness, smoothness, canonical overlap units, actual relative differential identification, nonboundary principal divisors, and local-order compatibility.

Concrete next cut: construct the genuine full projective principal divisor, including the three boundary valuations on the common function field, prove boundary compatibility and degree zero/product formula, and then supply concrete Picard/linear-system/Riemann–Roch data. The existing nonboundary principal-divisor degree is **not** generally zero; assigning arbitrary boundary coefficients to force the sum to zero would not prove the target mathematics.

Further genuine arithmetic remains after those geometric inputs: good-reduction/rank-zero constructions, primary kernels, geometric norm/pullback with composition [2], and Abel–Jacobi rational-point classification. Existing abstract consumer theorems retain these as inputs. The characteristic-three denominator-open equivalence does not cover all W-chart points: source explicitly supplies a counterexample to unconditional denominator avoidance.

See N25_N49_REVIEW.md for exact source links and N25_PLAN.md for the nearest-lemma follow-on plan. This delivery does not claim a compiled N25 replacement.

## 2. N49: raw order-49 Tate locus

FQN: `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`.
[Exact declaration, CyclicExclusion49.lean:43](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/CyclicExclusion49.lean#L43):

```lean
axiom no_raw_order49_tate_obstruction : ¬ RawOrder49TateObstruction
```

Expanded exact proposition:

```lean
¬ ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic
      (MazurProof.TateOriginDivision.W b c),
      b ≠ 0 ∧
        ((MazurProof.TateOriginDivision.W b c).preΨ' 49).eval 0 = 0 ∧
        ((MazurProof.TateOriginDivision.W b c).preΨ' 7).eval 0 ≠ 0
```

The proper order-seven exclusion is retained. The existing algebraic equivalence replaces the division-polynomial conditions by `bracket49 b c=0` and `c³-b²+bc≠0`, with `preΨ′₄₉(0)=b⁸⁰⁰ bracket49(b,c)`. It proves equivalence of obstruction representations, not impossibility.

Active users:
- direct `CyclicExclusion49.no_rational_point_of_order_49`, lines 45–50
- `MazurProof.no_order_49`, CyclicOrderAssembly:178
- private `no_order_bad_composite`, call at line 200
- common cyclic assembly/root route above

Equivalent tracked proof: **none found**. `TateOrder49Bridge.raw_order49_obstruction_iff` is an algebraic reformulation; the alternate composition shortcut still has a sorry and would not by itself establish exclusion; `X049DescentObstruction` has local certificates, not assembled rank zero/exhaustion.

The newer research notes retract the p=2-only route because Hensel-liftable Newton faces survive. That is reported research evidence, not an independent new kernel theorem here. The revised global route requires:
1. explicit Tate/order-49 map to X₀(49)
2. assembled rational-point/rank-zero proof for its elliptic target
3. identification of the rational target points as cusps and source cusp avoidance

The proposed map has degree 21. It is not birational from genus 69 to genus one.

## 3. Uniform prime tail

FQN: `MazurProof.no_prime_order_ge_23`.
[Exact declaration, CyclicOrderAssembly.lean:102–105](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/CyclicOrderAssembly.lean#L102-L105):

```lean
axiom no_prime_order_ge_23
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp23 : 23 ≤ p) :
    ¬ HasRationalPointOfOrder E p
```

`HasRationalPointOfOrder E p` means exactly `∃ P : (E⁄ℚ).Point, addOrderOf P=p` (TorsionDefs:20–21). The statement is uniform over all rational elliptic curves and all primes at least 23; finitely many prime checks cannot discharge it.

Active users:
- direct `MazurProof.no_prime_order_ge_17`, CyclicOrderAssembly:107–119, call at 112
- `MazurProof.mazur_prime_torsion_bound_sub`, lines 121–132, call at 127
- common cyclic assembly/root route above

Equivalent tracked proof: no noncircular uniform-tail theorem found in the inspected source. `mazur_prime_torsion_bound_sub` and `Axioms.no_rational_point_of_order_ge_17` consume this axiom. The older monolithic prime bound is itself axiomatic. The intended source-documented mathematics is formal immersion on X₀(p) and the Eisenstein-ideal uniform tail. A substantial uniform modular-curve/Jacobian development remains. This bounded search is not a semantic-equivalence decision over all Mathlib.

## Legacy assumptions excluded by the fresh root emission

`MazurProof.mazur_prime_torsion_bound` (CyclicOrderReduction:31–34):

```lean
axiom mazur_prime_torsion_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : Nat.Prime p)
    (hord : HasRationalPointOfOrder E p) :
    p ∈ ({2, 3, 5, 7} : Finset ℕ)
```

Its direct consumers remain confined to the legacy prime/composite reconstruction route. Active CyclicExclusion14/35 use its module's independent divisor-to-prime theorem instead. The current equivalent theorem `mazur_prime_torsion_bound_sub` still uses the uniform tail. Cleaning up the legacy declaration would not remove a custom axiom from the accepted root.

`MazurProof.mordell_weil_fg` (TorsionFinite:14–15) asserts `AddGroup.FG (E⁄ℚ).Point`. That module is outside the current root import closure; the actual finite-torsion proof uses TorsionFiniteFromOrderBound. The fresh emitted set confirms it is not a root assumption.

The old Kubert and other imported literal admissions likewise are not reachable sorryAx inputs of the freshly emitted accepted root. Source cleanup may be independently worthwhile, but is not next-boundary progress.

## Ranking and owned follow-on

Rank by present source maturity:
1. **N25:** actual source-to-target bridge, cusp avoidance and extensive geometric/local-divisor development; nearest concrete new lemma cut is full projective principal divisors/product formula
2. **N49:** useful algebra/local certificates, but global quotient map and arithmetic exhaustion still missing
3. **Prime ≥23:** largest missing uniform modular arithmetic framework

N25 vs N49 is tentative and is not a calendar-effort forecast: N25's remaining Picard/Riemann–Roch work is substantial; N49's proposed target is genus one. No unconditional substitute is ready for any of the three.

r5 assigns dot the nearest-boundary plan/candidate work, within the existing source-only role. Dot is continuing a bounded N25 exact-lemma assessment and will deliver genuine statement-preserving source candidates only when proved; it is not declaring the entire N25 arithmetic boundary closed or reassigning other lanes. Lead/Codex retains all compilation, kernel checks and integration. The status of actual remaining candidate proofs is **OPEN**, separate from this completed map.

## Synchronization and checks

- r5 receipt read and current full source SHA resolved: PASS
- C13 exact replacement and current tree continuity verified: PASS
- all 152 N25/N49-family blobs unchanged at 22f88d4: PASS
- custom boundary statements/users/meaning/equivalent-proof review: source-level PASS within stated scopes
- earlier 548 source-instance byte hashes: PASS, zero mismatches
- dot build/cache/emission/kernel work: NOT RUN
- lead aggregate and fresh root audit: PASS as reported in r5
- remaining arithmetic boundaries: THREE, OPEN

No lead integration is duplicated. This delivery updates the dot-owned communication/research artifacts only, following COMMS.md's comms/inbox convention. Old output-branch N13 source copies are not silently relabeled as the current accepted baseline; future source work reads accepted 22f88d4. The informal r4 “outbox + candidates” wording does not override the existing protocol. No main write, PR, merge, release or build occurred here.

