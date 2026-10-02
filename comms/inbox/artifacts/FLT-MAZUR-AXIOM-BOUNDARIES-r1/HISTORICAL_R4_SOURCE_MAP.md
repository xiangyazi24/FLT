# Historical r4 source boundary map at 6aef

STATUS UPDATE: Superseded as a current-status report by lead r5 at 22f88d43187caf0e57affcc6ded92cdf9b49714a. The N13 axiom has been discharged and the fresh root audit has exactly three custom axioms and no sorryAx. The four-axiom findings and pending language below describe only the deliberately frozen earlier pins, not current work. See SOURCE_MAP.md for the accepted state.


## Result and provenance

Requested source pin: `6aef0f8bdea96652f4879d0f74acd6bf189f306c` on `verify-sorry-restore`.
Dispatch: [lead r4](https://github.com/xiangyazi24/FLT/blob/7948ea628fbc38d552a2dac7ae0b0a47560d5635/comms/outbox/lead-FLT-N13-ENDPOINT-status-r4.md).
Research completed 2026-10-02 UTC.

Four custom axioms have explicit, active source-call paths to `MazurProof.mazur_torsion_bound` at the requested pin:
1. `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
2. `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`
3. `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`
4. `MazurProof.no_prime_order_ge_23`

This is a re-derived source map, **not emitted kernel closure**. The source import closure contains a fifth custom axiom, the legacy `MazurProof.mazur_prime_torsion_bound`, whose consumers are not on the displayed active route. Importing that declaration does not mean using it in the endpoint proof term.

The nearest arithmetic boundary is N13. Its exact unconditional replacement is already tracked on the delivered output branch and is present in later source [62968808d859114cb9ed61b478d1d692b3e71c52](https://github.com/xiangyazi24/FLT/commit/62968808d859114cb9ed61b478d1d692b3e71c52). It is absent from the requested 6aef tree. Even at 62968808, `CyclicExclusion13` still declares the original axiom. Thus the reported 57-module compilation does not by itself discharge the active endpoint's N13 boundary. Lead-owned aggregate verification, fresh axiom emission, and replacement wiring remain gates.

## Exact scan scope

- Retrieved full 6aef tree: 1,518 entries, not truncated
- Reconstructed `TorsionBound.lean` repository-local import closure: **213 files**, all read at the exact pin, all returned Git blob identities matched against the pinned tree
- 90 distinct external import paths, mainly Mathlib: not recursively re-audited
- Nested comments, line comments, and ordinary string literals removed before token scans
- Five literal custom-axiom declarations in that local import closure
- All 407 non-N13-file source blobs from earlier report [4109ba77](https://github.com/xiangyazi24/FLT/commit/4109ba77745784c1a9f8c4c7b304df4124bf5ac4) still match at 6aef; their old header inventory assisted discovery, but the current 213-file endpoint closure was subsequently read and scanned afresh
- Separately reconstructed the later N13 constructed endpoint's import closure at 62968808: **335 repository-local files**, all read and blob-matched; no literal `axiom`, `sorry`, `admit`, or `sorryAx` token remains after stripping comments/strings; 132 external imports not recursively re-audited
- That later N13 local import closure contains neither `CyclicExclusion13.lean` nor `CyclicOrderAssembly.lean`. This supports the proposed acyclic import wiring; it is not a claim about emitted axioms

The precise file/blob/header/flag inventories are in `SOURCE_AUDIT.json`. A separate byte-level verification recomputed Git blob SHA-1 and SHA-256 for all 548 fetched source instances (213 baseline + 335 later N13); all match their pinned tree identities, with zero mismatches. See `SOURCE_BLOB_VERIFICATION.json`. No Lean, lake, compilation, cache operation, proof emission, or runtime verification was run. The repository pins Lean `v4.31.0-rc2` and Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; these are source metadata, not a statement about the lead's runtime.

## Common active route

[Endpoint, TorsionBound:51–76](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TorsionBound.lean#L51-L76):

```lean
theorem mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionSet E).Finite ∧ (torsionSet E).ncard ≤ 16
```

The custom-axiom branches meet at `mazur_cyclic_order_bound_assembled` (CyclicOrderAssembly:204), then `mazur_cyclic_order_bound` (Axioms:289). From there the displayed endpoint source uses them in two places:
- `TorsionBound.n_in_mazur_list_of_structure` (private, line 20), called at line 59
- `TorsionFiniteFromOrderBound.torsionSet_subset_2520_torsion` (private, line 26) → `rational_torsion_finite` (line 41), called at endpoint line 53

Private names above are source-qualified labels; no generated kernel-private identifier is claimed.

## 1. N13 sextic cuspidality

FQN: `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`

[Declaration, CyclicExclusion13:36–37](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion13.lean#L36-L37):

```lean
axiom C13Sextic_affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1
```

Its mathematics is exactly rational affine-point classification on the sextic:
`Y² = X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.
Only X = 0 or -1 can occur; the equation then forces Y = ±1. It says nothing directly about the two projective points at infinity. [Definitions, N13CurveModel:25–30](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/N13CurveModel.lean#L25-L30)

Active source users:
- direct call in `C13Opt_rational_points_are_cuspidal`, CyclicExclusion13:41–52
- `no_F13_rational_solution`, same file:55–60
- `MazurProof.no_rational_point_of_order_13`, same file:65–72
- `MazurProof.no_order_13_prime`, CyclicOrderAssembly:87–90
- `mazur_prime_torsion_bound_sub`, same file:121–132
- common assembly route above

Equivalent tracked theorem:
- At 6aef, `N13RationalPointEndgame.CompatibleReduction.affine_x_is_cuspidal` (N13RationalPointEndgame:138) proves the same conclusion **with compatible reduction and separatedness inputs**; these hypotheses must not be erased in a claim of an unconditional proof
- `N13ConstructedReductionClassifier.compatibleReduction` is already constructed at 6aef, line 46
- Later 62968808 contains the exact unconditional `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal`, lines 35–37, with no extra premise. Its blob `596e3b9dbde0ce3b3dc39a9c1e5eb38b44831f46` equals the previously delivered output-branch version
- The same later CyclicExclusion13 blob remains `560a0ac2efd8354714cbd61b6489ed25fd2b5448`, still axiomatic. Do not equate candidate compilation with removal from the root

See `N13_ACCEPTED_CHAIN.md` for dependency-ordered exact statements and the minimal proposed replacement.

## 2. N25 primitive Tate obstruction

FQN: `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`

[Declaration, CyclicExclusion25:47](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion25.lean#L47):

```lean
axiom no_explicit_order25_obstruction : ¬ ExplicitOrder25Obstruction
```

Expanded statement, retaining every hypothesis:

```lean
¬ ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic
      (MazurProof.TateOriginDivision.W b c),
      b ≠ 0 ∧ b - c ≠ 0 ∧
        MazurProof.TateOrder25Factor.F25 b c = 0
```

The Tate curve is `y² + (1-c)xy - by = x³ - bx²`. `F25` is the explicit degree-40 factor remaining after removing the proper-order-five factor from the order-25 division polynomial. The nonsingularity and F5 = b-c nonzero conditions are essential; the target is not unrestricted polynomial nonvanishing. Definitions and compact factorization are linked in `N25_N49_REVIEW.md`.

Active users: direct `CyclicExclusion25.no_rational_point_of_order_25` (49–54) → `MazurProof.no_order_25` (CyclicOrderAssembly:170) → private `no_order_bad_composite` (184–200, branch at 197) → common assembly.

Equivalent tracked proof: **none found** in the complete 152-file N25/N49 family review. Existing genus-four canonical source bridge gives an actual noncuspidal target point, but not target rational-point exhaustion. Current source has actual properness, smoothness, relative differentials, and local divisor infrastructure. The older “identify the overlap unit” roadmap task is already proved and must not be repeated.

Current concrete frontier: full projective principal divisors with boundary compatibility and degree-zero/product formula; then actual Picard/Riemann–Roch/linear-system inputs, rational rank-zero/good-reduction constructions, and geometric norm/pullback and Abel–Jacobi classification. Abstract bookkeeping theorems retain these inputs. A characteristic-three denominator-open equivalence does not cover all W-chart points; source supplies a counterexample to unconditional denominator avoidance.

## 3. N49 raw Tate obstruction

FQN: `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`

[Declaration, CyclicExclusion49:43](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion49.lean#L43):

```lean
axiom no_raw_order49_tate_obstruction : ¬ RawOrder49TateObstruction
```

Expanded statement:

```lean
¬ ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic
      (MazurProof.TateOriginDivision.W b c),
      b ≠ 0 ∧
        ((MazurProof.TateOriginDivision.W b c).preΨ' 49).eval 0 = 0 ∧
        ((MazurProof.TateOriginDivision.W b c).preΨ' 7).eval 0 ≠ 0
```

This excludes nonsingular Tate data with an order-49 vanishing division polynomial and a nonvanishing proper order-seven factor. The tracked equivalent *obstruction representation* uses `bracket49 = 0` and `c³-b²+bc ≠ 0`; equivalence of representations does not prove either obstruction impossible.

Active users: direct `CyclicExclusion49.no_rational_point_of_order_49` (45–50) → `MazurProof.no_order_49` (CyclicOrderAssembly:178) → private `no_order_bad_composite` (branch at 200) → common assembly.

Equivalent tracked proof: **none found** in the complete N25/N49 family review. `TateOrder49Bridge.raw_order49_obstruction_iff` is algebraic reformulation only. `RationalPointsN49Composition.composition_identity_sorry` is still admitted and, even proved, would not be exclusion. `X049DescentObstruction` contains local certificates, not assembled rank zero or rational-point exhaustion.

Current research documents explicitly retract the p=2-only closure route because some Newton faces lift to actual Q₂ points; this is reported research evidence, not newly kernel-verified here. The revised global route needs an explicit degree-21 map to X₀(49), assembled arithmetic exhaustion of that elliptic curve, and source cusp avoidance. A genus-69 to genus-one map is not birational.

## 4. Uniform prime tail

FQN: `MazurProof.no_prime_order_ge_23`

[Declaration, CyclicOrderAssembly:102–105](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicOrderAssembly.lean#L102-L105):

```lean
axiom no_prime_order_ge_23
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp23 : 23 ≤ p) :
    ¬ HasRationalPointOfOrder E p
```

Here `HasRationalPointOfOrder E p` is exactly `∃ P : (E⁄ℚ).Point, addOrderOf P = p` (TorsionDefs:20–21). The statement is uniform in all rational elliptic curves and all primes at least 23. It does not follow from finitely many small-prime checks.

Active users: direct `no_prime_order_ge_17` (CyclicOrderAssembly:107–119, call at 112) → `mazur_prime_torsion_bound_sub` (121–132, call at 127) → common assembly.

Equivalent tracked proof: no noncircular uniform-tail theorem found in the inspected source. The prime-bound theorem `mazur_prime_torsion_bound_sub` and `Axioms.no_rational_point_of_order_ge_17` both already consume this tail, so using them back here is circular. The older monolithic prime bound below is itself an axiom. The source documents label the intended missing mathematics formal immersion on X₀(p) and the Eisenstein-ideal uniform tail. This is a substantial modular-curve/Jacobian arithmetic development, not a finite computation or a short substitution. The bounded search does not assert a semantic-equivalence decision over all Mathlib.

## Imported legacy axioms and false positives

### Imported but not on the displayed active route

FQN: `MazurProof.mazur_prime_torsion_bound`, [CyclicOrderReduction:31–34](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicOrderReduction.lean#L31-L34):

```lean
axiom mazur_prime_torsion_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : Nat.Prime p)
    (hord : HasRationalPointOfOrder E p) :
    p ∈ ({2, 3, 5, 7} : Finset ℕ)
```

It is used by `not_has_point_of_order_of_large_prime_dvd` (same file:65–74) and `mazur_cyclic_order_bound_from_prime_and_composite_exclusions` (114–138), then its alias (143–149). No other code reference to those legacy consumers was found in the current 213-file source closure. CyclicExclusion14/35 instead use the independently proved `exists_point_of_prime_order_of_dvd` from the same module. The active assembly calls the distinct `mazur_prime_torsion_bound_sub`.

An exact-statement theorem counterpart already exists: `mazur_prime_torsion_bound_sub`. Replacing the legacy declaration by it would require acyclic import restructuring and would merely exchange this unused monolithic axiom for the active N13/uniform-tail boundary dependencies. It is not endpoint progress and is not the selected next task.

### Outside this endpoint import closure

`MazurProof.mordell_weil_fg`, TorsionFinite:14–15:

```lean
axiom mordell_weil_fg (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E⁄ℚ).Point
```

The actual endpoint imports `TorsionFiniteFromOrderBound`, not `TorsionFinite`; the pointwise cyclic-bound route proves finiteness without invoking Mordell–Weil. Do not count this sixth MazurProof source axiom as an established endpoint dependency.

The wider import scan also sees seven literal sorry tokens in old Kubert, scratch DischargeN14, and FLT/EllipticCurve/Torsion declarations. This does not establish any is emitted-reachable. It also explains why the older filename-bounded “three sorry sites” inventory was never a full import or proof closure. Their admission locations are recorded in SOURCE_AUDIT.json solely for scope honesty.

## Distance-to-proof ranking

This ranking concerns current proof maturity, not predicted calendar effort:

1. **N13:** exact unconditional replacement already tracked in later source, with full 57-module individual compilation reported. Remaining work is lead-owned aggregate/kernel validation and minimal wiring
2. **N25:** extensive genuine geometric and local-divisor source development, actual source-to-target map and cusp avoidance; substantial global divisor/Picard/Riemann–Roch/rank-zero input remains
3. **N49:** algebraic reduction and local certificates exist, but the needed global quotient map and arithmetic exhaustion are not assembled; old local-only plan is blocked
4. **Prime ≥23:** uniform modular arithmetic theorem; largest missing mathematical framework among these inspected routes

The N25/N49 ordering is tentative: N25 is more mature in source, while N49's proposed target is only genus one and could ultimately require less new machinery. Neither is wiring-only. No new lane or ownership assignment is inferred.

## Acceptance and delivery gates

- Source/tree/header/token review: PASS within the scopes above
- Candidate statement comparison: PASS at source level; exact N13 proposition preserved
- New Lean declarations or scaffolding: NONE
- Lean compilation, kernel checking, emitted axioms, declaration-level closure, aggregate acceptance: NOT RUN by dot; lead-owned
- Old August 12 olean and August 20 audit: not treated as current evidence
- Whole Mazur completion: NOT CLAIMED

COMMS.md requires dot results in comms/inbox on its own branch, while lead r4 informally says “outbox + candidates.” This delivery follows the established inbox/artifact convention and flags the wording discrepancy rather than writing into the lead's outbox. No candidate source duplication is necessary: the closest exact proof is already tracked.

