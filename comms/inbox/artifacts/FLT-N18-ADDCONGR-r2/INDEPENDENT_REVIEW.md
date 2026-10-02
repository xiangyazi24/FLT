# Independent source-only N18 addition-congruence review

Reviewed candidate files under `output/FLT/Assumptions/MazurProof/` against the supplied `input/` files, associated with source pin `4017da66cbb1b8deff6da7116c7af5de540e1908`.

## Verdict

No concrete mathematical or refactor defect found in the inspected candidate. This is a source review, **not evidence of successful Lean elaboration or kernel verification**. No Lean executable, build, cache operation, or remote mutation was performed.

## Preservation and import graph

- A direct text comparison confirms that the original toolbox through `val_coords` is preserved byte-for-byte in `N18AddCongrBasic`, apart from the introductory documentation and closing placement.
- Every declaration and proof body in `N18AddCongrProof`, beginning at `open scoped Classical`, is byte-identical to the supplied original. Its import now selects Basic rather than AddCongr.
- The public `add_congr` signature, including both hypotheses and the complete conclusion, is byte-identical to the original. Its namespace remains `MazurProof.N18Block5Instantiation.AddCongr` (candidate AddCongr22–36).
- The four-module dependency chain is `AddCongr → Wired → Proof → Basic`, with no cycle among those modules. Basic retains the original upstream imports; inspected `N18Block5Instantiation` has no direct import back into these modules. The entire upstream transitive import graph was not available in the supplied local snapshot and was not independently reconstructed.
- Removing Wired's duplicate private `xCoord` makes its hypotheses use the existing public parent declaration. The inspected upstream definition (input Block5Instantiation62–64) has the same zero/some equations. The final exact application therefore targets the intended coordinate function without a private/public conversion seam.

## Wiring and remaining verification risk

The origin branches return zero error. For finite points the helpers establish nonzero coordinates before dispatch. The equal-x split distinguishes inverse points from equal points; the latter uses `Y_eq_of_Y_ne` before invoking the tangent branch. The inverse negation orientation and the tangent non-self-inverse orientation are consistent with their branch signatures. The tangent `simpa only [two_mul, sub_sub]` matches the doubled-parameter expression to repeated subtraction and the doubled valuation to addition.

Dependent point equality at Wired80–87, proof equality at Wired91, and the simplification at Wired92–93 are elaboration-sensitive sites. Inspection found no concrete error there, but their acceptance is unverified. The final theorem calls Wired directly, and the branch source does not call the original placeholder `add_congr`; the refactor removes that proof dependency. This does not certify upstream axiom dependencies or complete all `FormalKernelData` fields.

## Countertheorem and geometry

`not_add_congr_signature` negates the historical hypotheses `1 ≤ v(zP)` and `1 ≤ v(zQ)` with a bare valuation-bound conclusion (input Proof1261–1265). Current `add_congr` instead assumes each point is zero or has `ordPi(x)<0`, and permits zero error explicitly (candidate AddCongr31–35). Both differences matter.

The old counterexample is not rescued by adding only a zero-error disjunction. Its two input z-values have valuation 1; their sum point has z-value `1/2`, a unit (input Proof1117–1223). Subtracting two positive-valuation terms from that unit leaves a **nonzero** unit. The proof's strict-domination facts justify nonzeroness; `ordPi(error)=0` alone would not, because `ordPi(0)=0`.

The sufficient concrete geometric explanation is valuation-based: both input points have `v(x)=1` and `v(y)=0` (input Proof1152–1154,1184–1190,1197–1209). Thus z is small because the numerator is small and the denominator is a unit, while both points fail the corrected near-origin condition. True finite near-origin points instead satisfy `v(x)=-2v(z)` and `v(y)=-3v(z)` (candidate Basic155–159). No explicit residue-point or singularity assertion is needed for this conclusion.

The candidate documentation correctly distinguishes the historical countertheorem from the current theorem and removes the old claim that these witnesses were formal-kernel points.

## Reviewed candidate SHA-256

- `N18AddCongrBasic.lean`: `22316c94058df9f8ac6120863f40555f286b0088f368be46a7269e2cdaec5c4c`
- `N18AddCongrProof.lean`: `e741869abf41b6386f837dd9110eb20a33ec52a91f69f120bb9cf2566bb09810`
- `N18AddCongrWired.lean`: `5020c806e13a8f46c907f5f15635241ee8e8199727d49da9739b1ee5a355b30c`
- `N18AddCongr.lean`: `412341d84601cc7a3fda6a80997328affa90d5575034890d2a396b3e4f724d60`
