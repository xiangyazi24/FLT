TASK_ID: FLT-N18-ADDCONGR
REVISION: 2
TYPE: RESULT
STATUS: SOURCE_CANDIDATE_READY_FOR_LEAD_COMPILATION
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 4017da66cbb1b8deff6da7116c7af5de540e1908
DISPATCH_COMMIT: efe5d9830fcf6504073abf4b6c6ebb2eb112b22f
WRITE_SCOPE: research-dot/flt-collaboration-20261001
SUPERSEDES: read-only N18 ownership/source query only

## 1. Semantic result: the current statement is not refuted

N18AddCongrProof.not_add_congr_signature negates the OLD signature with hypotheses 1 <= v(zParam P) and 1 <= v(zParam Q), and a bare valuation inequality. The current AddCongr.add_congr instead assumes P = O or ordPi(xCoord P) < 0, likewise Q, and concludes error = 0 OR the inequality. Its current proposition is preserved byte-for-byte by this candidate.

These are two independent changes, and the hypotheses matter. In the explicit old counterexample P = generator21 and Q = torsionAffine 5, both input z-values have valuation 1, but their sum is torsionAffine 6 with z = 1/2 of valuation 0. The error is a NONZERO unit, so a zero-error disjunction alone does not repair the old signature. The proof's coordinate calculations give v(x) = 1 and v(y) = 0 for each input; they are finite integral points away from O and fail the current x-negative hypothesis. Genuine finite near-O points instead obey v(x) = -2 v(z), v(y) = -3 v(z), as proved by val_coords.

The comments that called the old counterexample "kernel points" or said the proposed/current statement cannot be proved were stale. They are corrected here. The original countertheorem and all seven lead-accepted theorem bodies remain unchanged.

## 2. Candidate and import-cycle repair

Four source files are supplied as one atomic overlay:

1. N18AddCongrBasic.lean: moves the original parameter/valuation toolbox and val_coords below the branch proofs. Namespace, declaration statements and proof bodies are byte-identical; only its introductory comment changes.
2. N18AddCongrProof.lean: switches its first import from N18AddCongr to N18AddCongrBasic and fixes the stale semantic overview. Everything from open scoped Classical onward is byte-identical to the lead source.
3. N18AddCongrWired.lean: removes the colliding private xCoord declaration and directly uses the identical existing public N18Block5Instantiation.xCoord. Branch proofs are unchanged.
4. N18AddCongr.lean: imports Wired and closes the old theorem, under its exact original name and proposition, by N18Block5Instantiation.add_congr_wired P Q hP hQ. The former admission is removed rather than renamed or retained elsewhere.

The import direction is AddCongr -> Wired -> Proof -> Basic. Importing the branch proof back into the unsplit original AddCongr would create a cycle, so the toolbox split is necessary for this direct closure. A bounded import-header trace resolves 44 project modules with no cycle. This is not a full source-admission audit of every imported module.

All four candidate code bodies have zero axiom/sorry/admit/sorryAx tokens after comment/string removal. Independent source review found no concrete statement or wiring defect. Dependent constructor equality and the tangent simplification remain elaboration-sensitive and require Lean verification.

## 3. Does the endpoint depend on N18?

There are two different scopes:

- The constructed N13 affine endpoint delivered at d7afa66f690a038ef82e9fe261bf1b98f4cf18c3 does NOT import N18AddCongr, N18AddCongrProof, N18AddCongrWired, N18Block5Instantiation, or the actual N18 curve/arithmetic pipeline. Its 335-module audited closure uses only N18RouteC_Separated and N18RouteC_PushPull from the N18-named modules. Those are generic additive-group/separatedness helpers. The 29e80 -> 4017 source comparison adds only Proof and Wired, so the recorded N13 dependencies are unchanged.
- The full Mazur torsion-bound endpoint DOES depend on order-18 exclusion: TorsionBound -> TorsionFiniteFromOrderBound -> Axioms -> CyclicOrderAssembly -> no_order_18 -> N18GoodModelAssembly.no_five_descent_solution, together with CyclicExclusion18.order18_to_five_descent. This is a separate arithmetic route. It would be false to claim the full Mazur endpoint is N18-independent.

Import presence is not itself proof-term dependence on the old admitted AddCongr.add_congr. N18GoodModelAssembly imports AddCongr and its valuation wrapper, but its good-model route is distinct from the original E0 near-O statement. This packet does not claim a complete emitted-axiom audit of the full Mazur endpoint or that repairing this helper alone completes N18 or Mazur.

## 4. Validation and integration gate

The lead reported that the seven original Proof theorems built with [propext, Classical.choice, Quot.sound]. That report covers the pinned original module, not this new import context or repaired Wired/final closure.

By dot: exact source Git blobs PASS; statement/body preservation PASS; four-file admission scan PASS; 44-module import-header cycle check PASS; independent source review COMPLETE. Lean build, project execution, dependency-cache work and emitted-axiom checks NOT RUN.

Apply all four files together, rebuild Basic, Proof, Wired and AddCongr in that order, then run the supplied VALIDATION.lean. Inspect emitted axioms for the public wired and original-name endpoints and the retained countertheorem. Rebuild affected consumers such as N18VpiWrapper/N18GoodModelAssembly as appropriate. Only standard Lean axioms count as acceptance. Lead owns compilation, acceptance, and integration.

No main-branch mutation, PR, release, deployment, or build is performed by this packet.

Updated: October 1, 2026, 7:01 p.m. America/Chicago.
