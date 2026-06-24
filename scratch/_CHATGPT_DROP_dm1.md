# Q137 (dm1): Current-state audit of Mazur `|T| ≤ 16` formalization

Audit target:

```text
branch: scratch
repo:   xiangyazi24/FLT
paths:  FLT/Assumptions/MazurProof/ + FLT/EllipticCurve/Torsion.lean
```

I checked the actual branch state through the GitHub connector.  The key finding is that the branch is **not** currently in the six-axiom Mazur-proof-checklist state described in `MAZUR_AXIOM_CHECKLIST.md`.  On the `scratch` branch I could not fetch `FLT/Assumptions/MazurProof/` at all: the GitHub contents endpoint reports it as missing.  The repository still has the older monolithic assumption file

```text
FLT/Assumptions/Mazur.lean
```

and `FLT/EllipticCurve/Torsion.lean` still contains several literal `sorry`s in the n-torsion/Galois-representation infrastructure.

So the honest current-state summary is:

```text
There is no axiom-free MazurProof stack in the checked branch.
The six checklist axioms A1--A6 are not present as current declarations in the requested path.
The effective current top-level Mazur assumption is still `axiom Mazur_statement`.
The keystone torsion infrastructure K1/K2/K3 is still represented by sorries in `Torsion.lean`.
The downstream Frey/Mazur irreducibility bridge is still a `sorry` in `FreyCurve/Contradiction.lean`.
```

## Files actually read

### `FLT/Assumptions/Mazur.lean`

This file contains the old monolithic statement:

```lean
/-- Mazur's bound for the size of the torsion subgroup of an elliptic curve
 over the rationals . -/
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

There is no proof body and no reference to a `MazurProof` submodule in this file.

### `FLT/EllipticCurve/Torsion.lean`

This file still has these literal `sorry`s:

```lean
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n) := sorry

theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := sorry

noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry

noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul := sorry
      mul_smul := sorry
      smul_zero := sorry
      smul_add := sorry

def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
```

The theorem

```lean
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n))
```

is not itself a `sorry`, but it depends directly on `group_theory_lemma` and `n_torsion_card`.

### `FLT/FreyCurve/Contradiction.lean`

This file still has the downstream Mazur bridge as a literal `sorry`:

```lean
theorem Mazur_Frey (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry
```

This file imports `FLT.EllipticCurve.Torsion`, so the `galoisRep` construction in `Torsion.lean` is on the path to `Mazur_Frey`.

### `FLT/Assumptions/MazurProof/`

I attempted direct repository-content access to this directory and to plausible files such as:

```text
FLT/Assumptions/MazurProof/Basic.lean
FLT/Assumptions/MazurProof/Main.lean
```

The directory/file path was not found on the `scratch` branch.  Therefore the current audit cannot report theorem/axiom status inside `MazurProof/`: in the checked branch, that directory is not present.

## 1. Status of the six checklist top-level axioms A1--A6

Because `FLT/Assumptions/MazurProof/` is absent in the checked branch, the checklist axioms do not currently exist as declarations there.  The current code surface is the older single axiom `Mazur_statement`.

| Checklist item | Current checked-branch status | Notes |
|---|---:|---|
| A1 `rational_torsion_two_invariant_factors` | Not present as a declaration in checked files | Not discharged; no `MazurProof/` module present. |
| A2 `weil_pairing_primitive_root` | Not present as a declaration in checked files | Not discharged; no Miller/Weil pairing proof in the checked Mazur surface. |
| A3 `no_rational_point_of_order_ge_17` | Not present as a declaration in checked files | Not discharged; this is essentially a core Mazur/modular-curve theorem. |
| A4 `Z2xZ14` exclusion | Not present as a declaration in checked files | Not discharged. |
| A5 `Z2xZ16` exclusion | Not present as a declaration in checked files | Not discharged. |
| A6 `mordell_weil_fg` | Not present as a declaration in checked files | Not discharged; old monolithic `Mazur_statement` bypasses it. |

Effective current top-level Mazur axiom:

| Effective current declaration | Status |
|---|---:|
| `axiom Mazur_statement` in `FLT/Assumptions/Mazur.lean` | Still an axiom |

So the answer to “which of the six top-level custom axioms are now discharged to theorems?” is: **none are present/discharged in the checked branch**.  The branch is still using a monolithic `Mazur_statement` axiom, plus separate sorries in torsion infrastructure and the Frey/Mazur bridge.

## 2. Residual seam-sorryAx under discharged items

There are no discharged A1--A6 items in the checked branch, so there are no residual seam dependencies under discharged A1--A6 theorems to report.

For the existing torsion infrastructure, the residual seams are still explicit:

| Infrastructure item | Current declaration | Residual obligations |
|---|---|---|
| K1 `#E[n] = n²` over separably/algebraically closed field | `WeierstrassCurve.n_torsion_card` | Literal `sorry`; needs SEAM1 separability, SEAM2 x-coordinate/nsmul criterion, root realization/counting. |
| K2 rank-2 geometric n-torsion | `WeierstrassCurve.n_torsion_dimension` | The theorem body exists but rests on `n_torsion_card` and `group_theory_lemma`, both currently sorry-backed. |
| K3 finite module/Galois API | `Module.Finite`, `galoisRepresentation`, `galoisRep` | Literal sorries remain. |
| Group theory conversion from cardinality to `(ZMod n)^r` | `group_theory_lemma` | Literal `sorry`. |

## 3. Full list of remaining Mazur/torsion obligations found

### A. Hard axiom still present

1. `FLT/Assumptions/Mazur.lean`

   ```lean
   axiom Mazur_statement ... : torsion.ncard ≤ 16
   ```

   This is the only actual Mazur theorem statement present in the checked assumptions file.

### B. Torsion infrastructure sorries

2. `FLT/EllipticCurve/Torsion.lean`

   ```lean
   theorem WeierstrassCurve.n_torsion_finite ... := sorry
   ```

   Needed to make torsion groups finite over base fields and to support continuity/finite-module instances.

3. `FLT/EllipticCurve/Torsion.lean`

   ```lean
   theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] ... : Nat.card (E.nTorsion n) = n^2 := sorry
   ```

   This is K1.  It is the main division-polynomial counting theorem.

4. `FLT/EllipticCurve/Torsion.lean`

   ```lean
   theorem group_theory_lemma ... : Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → ZMod n)) := sorry
   ```

   This is the finite-abelian-group/invariant-factor conversion used by `n_torsion_dimension`.

5. `FLT/EllipticCurve/Torsion.lean`

   ```lean
   noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry
   ```

6. `FLT/EllipticCurve/Torsion.lean`

   ```lean
   WeierstrassCurve.galoisRepresentation.one_smul := sorry
   WeierstrassCurve.galoisRepresentation.mul_smul := sorry
   WeierstrassCurve.galoisRepresentation.smul_zero := sorry
   WeierstrassCurve.galoisRepresentation.smul_add := sorry
   ```

   These should be small API proofs from `Affine.Point.map_id`, `Affine.Point.map_map`, and map preserving the group law.

7. `FLT/EllipticCurve/Torsion.lean`

   ```lean
   def WeierstrassCurve.galoisRep ... := sorry
   ```

   This bundles the finite torsion module plus the Galois action into the project’s `GaloisRep` structure.  The file comment says the missing part should be continuity, following from finiteness.

### C. Downstream Mazur/Frey bridge sorry

8. `FLT/FreyCurve/Contradiction.lean`

   ```lean
   theorem Mazur_Frey (P : FreyPackage) :
       haveI : Fact P.p.Prime := ⟨P.pp⟩
       GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) := sorry
   ```

   This is currently the actual bridge from “Mazur” to the Frey-curve Galois representation in the FLT contradiction file.

### D. Missing directory/module

9. `FLT/Assumptions/MazurProof/`

   Not present in the checked branch.  Any checklist obligations in that directory are not currently part of the Lean code surface of this branch.

## 4. Dependency DAG

Current actual dependency graph:

```text
FLT.Assumptions.Mazur
└─ axiom Mazur_statement
   └─ currently not wired into `FreyCurve/Contradiction.lean` in the files read

FLT.EllipticCurve.Torsion
├─ n_torsion_finite                       [sorry]
├─ n_torsion_card                         [sorry, K1]
│  ├─ SEAM1 preΨ'_separable               [not present in current Torsion.lean]
│  ├─ SEAM2 nsmul_eq_zero_iff_ΨSq_eval     [not present in current Torsion.lean]
│  ├─ root realization / non-2 branch      [not present in current Torsion.lean]
│  └─ root counting over IsSepClosed        [not present in current Torsion.lean]
├─ group_theory_lemma                     [sorry]
│  └─ finite abelian group/invariant-factor argument
├─ n_torsion_dimension
│  ├─ depends on n_torsion_card            [sorry-backed]
│  └─ depends on group_theory_lemma         [sorry-backed]
├─ Module.Finite (ZMod n) (E.nTorsion n)  [sorry]
├─ galoisRepresentation action laws        [4 small sorries]
└─ galoisRep                              [sorry]
   ├─ depends on Module.Finite / finiteness / topology
   └─ used by FreyCurve.Contradiction.Mazur_Frey

FLT.FreyCurve.Contradiction
└─ Mazur_Frey                             [sorry]
   ├─ depends on P.freyCurve.galoisRep
   ├─ should use a Mazur torsion-bound theorem or stronger classification theorem
   └─ feeds FreyPackage.false and Wiles_Taylor_Wiles
```

Checklist-intended dependency graph, not currently instantiated in the checked branch:

```text
A6 Mordell-Weil finite generation
└─ rational torsion finite
   └─ A1 rational torsion two invariant factors
      ├─ A2 Weil pairing primitive root       (uses K1/K2/K3 + SEAM3)
      ├─ A3 no rational point order ≥ 17      (Mazur modular-curve input)
      ├─ A4 exclude Z/2 × Z/14                (Mazur modular-curve input)
      └─ A5 exclude Z/2 × Z/16                (Mazur modular-curve input)
         └─ Mazur bound |T| ≤ 16
            └─ Mazur_Frey / irreducibility bridge
```

## 5. Critical path to a fully axiom-free `|T| ≤ 16`

There are two possible interpretations of “fully axiom-free”.

### Route 1: Prove the old monolithic `Mazur_statement`

This is the current code-surface route because `FLT/Assumptions/Mazur.lean` exposes exactly that axiom.

Critical path:

```text
Prove `Mazur_statement` directly
  → rewrite `FreyCurve/Contradiction.Mazur_Frey` to use it
  → discharge `Mazur_Frey`
  → separately clean `Torsion.lean` sorries needed for `galoisRep`
```

This route is conceptually simple at the API level but mathematically enormous: it hides all of Mazur’s theorem behind one theorem.

### Route 2: Reintroduce and complete the six-axiom checklist stack

This is the roadmap route described by the prompt, but it is not currently present on the checked branch.

Critical path:

```text
1. Add/restablish `FLT/Assumptions/MazurProof/` modules.
2. Prove or explicitly stage A1--A6 as theorem targets.
3. Finish K1/K2/K3 in `Torsion.lean`:
   K1: n_torsion_card = n²
   K2: n_torsion_dimension / rank-2 geometric torsion
   K3: finite module + Galois representation API
4. Prove A2 Weil-pairing primitive-root theorem from K1/K2/K3 + Miller/Weil pairing machinery.
5. Prove or assume-then-replace A3/A4/A5 modular-curve exclusions.
6. Combine A1--A6 into `Mazur_statement` or directly into the Frey irreducibility theorem.
7. Replace `Mazur_Frey := sorry` with the actual proof.
```

The current shortest technical critical path inside the existing files is:

```text
n_torsion_card
  + group_theory_lemma
  → n_torsion_dimension
  → Module.Finite + galoisRepresentation + galoisRep
  → usable p-torsion Galois representation
  → Mazur_Frey
```

But this only gives the Galois-representation infrastructure.  It does **not** prove the Mazur bound itself.  The bound/classification input is still the old `Mazur_statement` axiom unless the missing `MazurProof/` stack is added.

## 6. Relative difficulty / size estimates

### Small / API cleanup

| Item | Estimate | Notes |
|---|---:|---|
| `galoisRepresentation.one_smul` | Small | Should follow from `Affine.Point.map_id`. |
| `galoisRepresentation.mul_smul` | Small | Should follow from `Affine.Point.map_map`. |
| `galoisRepresentation.smul_zero` | Small | Map is an additive monoid hom. |
| `galoisRepresentation.smul_add` | Small | Map is an additive monoid hom. |
| `Module.Finite (ZMod n) (E.nTorsion n)` once finite/cardinality is available | Small–medium | Likely straightforward from finiteness/equiv. |
| `galoisRep` continuity once finite torsion/action laws are available | Small–medium | File comment says continuity follows from finiteness. |

### Medium / group theory

| Item | Estimate | Notes |
|---|---:|---|
| `group_theory_lemma` | Medium–large | Needs finite abelian group decomposition or a specialized torsion-card-to-free-`ZMod n` argument. Could be short if Mathlib has exactly the right finite-module structure theorem; otherwise substantial. |
| `n_torsion_finite` | Medium | Could follow from embedding into algebraic closure plus finite `n_torsion_card`, or from polynomial root bounds. Needs careful field/base-change API. |

### Large / division-polynomial keystone

| Item | Estimate | Notes |
|---|---:|---|
| `n_torsion_card` K1 | Large | Needs SEAM1 separability, SEAM2 nsmul/x-coordinate criterion, root realization, root counting, and 2-torsion handling. This is the main technical Lean burden currently visible in `Torsion.lean`. |
| SEAM1 `preΨ'_separable` | Large | From the previous SEAM discussion: local dual-number/tangent or equivalent resultant/Wronskian infrastructure. Not currently wired into `Torsion.lean`. |
| SEAM2 `nsmul_eq_zero_iff_ΨSq_eval` | Large | Needs coordinate-ring congruences and point/multiplication formulas. |
| SEAM3 Miller/Weil pairing | Large | Needed for A2; not part of current `Torsion.lean`. |

### Very large / Mazur theorem proper

| Item | Estimate | Notes |
|---|---:|---|
| A3 no rational point of order ≥ 17 | Very large | Core modular-curve/Mazur input. |
| A4 exclude `Z/2 × Z/14` | Very large | Core modular-curve/Mazur input. |
| A5 exclude `Z/2 × Z/16` | Very large | Core modular-curve/Mazur input. |
| A6 Mordell-Weil finite generation | Very large | Major arithmetic theorem unless imported from a separate library. |
| Full proof of `Mazur_statement` | Very large | Encompasses classification or enough of it for the bound. |
| `Mazur_Frey` from the bound/classification | Medium once inputs exist | Needs Frey-specific torsion facts plus the Galois representation infrastructure. |

## 7. Honest distance from done

The current checked branch is **not close to an axiom-free Mazur bound**.  It is not merely one remaining `sorry`.  The actual state is:

```text
* Old monolithic Mazur axiom still present.
* Six-axiom MazurProof decomposition absent from the checked branch.
* K1/K2/K3 torsion infrastructure still sorry-backed.
* Downstream `Mazur_Frey` bridge still a `sorry`.
```

The most realistic next steps are:

1. Decide whether the active code path is the old monolithic `Mazur_statement` or the six-axiom `MazurProof/` checklist architecture.
2. If using the checklist architecture, add or restore `FLT/Assumptions/MazurProof/` so the declarations exist and are imported.
3. Independently finish the visible `Torsion.lean` infrastructure because it is needed for p-torsion Galois representations regardless of how the Mazur bound is packaged.
4. Treat `n_torsion_card` as the current keystone blocker in code, with SEAM1/SEAM2/root-realization as its internal critical path.
5. Treat A3/A4/A5/A6 as the mathematically largest remaining assumptions once the torsion infrastructure is finished.

## 8. Compact status table

| Layer | Current status on `scratch` | Blocking declarations |
|---|---|---|
| Old Mazur bound | Still axiom | `Mazur_statement` |
| Six-axiom MazurProof stack | Not present in checked branch | Directory/path absent |
| K1 `#E[n]=n²` | Sorry | `n_torsion_card` |
| K2 rank-2 geometric torsion | Theorem body exists but sorry-backed | `n_torsion_card`, `group_theory_lemma` |
| K3 finite/Galois API | Sorry-backed | `Module.Finite`, action laws, `galoisRep` |
| Frey/Mazur irreducibility bridge | Sorry | `Mazur_Frey` |
| Final FLT contradiction | Formal wrapper exists but depends on `Mazur_Frey` | `FreyPackage.false`, `Wiles_Taylor_Wiles` rely on `Mazur_Frey` |
