# Q460 (dm2): `formalU_eq` status

I could not close the `formalU_eq` sorry in this session because the requested source file is not present on the remote branch that I can access through the GitHub connector.

## What I checked

- Repository: `xiangyazi24/FLT`
- Branch requested: `scratch`
- Requested file: `scratch/FormalGroupW.lean`
- Connector fetch attempted against `ref = scratch`

Result:

```text
GitHub.fetch_file(
  repository_full_name = "xiangyazi24/FLT",
  path = "scratch/FormalGroupW.lean",
  ref = "scratch"
)

=> 404 Not Found
```

The branch itself does exist: `compare_commits(main, scratch)` succeeds and reports `scratch` as diverged from `main`.

I also verified that the local runtime available to this ChatGPT session does not have `gh`, `lean`, or `lake`, so I cannot SSH to `uisai2`, clone from GitHub, or run the Lean build locally from here. The only reliable write path available here is the GitHub connector.

## Consequence

No code patch was made to `scratch/FormalGroupW.lean`, because updating a nonexistent remote file would mean inventing the file contents rather than closing the actual sorry at line 217.

## Intended proof shape once the file is available

Based on the request description, the patch should stay local to the `formalU_eq` proof after

```lean
ext n
cases n
```

and the `formalUCoeff_succ` unfold/simp step. The remaining goals should be closed by natural-number arithmetic and finite-sum congruence, roughly in this style:

```lean
  · -- zero coefficient case
    simp [formalU]
  · -- successor coefficient case
    rw [formalUCoeff_succ]
    simp only [coeff_one, coeff_X, coeff_C, coeff_mul, coeff_pow]
    split_ifs with h
    · -- arithmetic/index-alignment branch
      congr 1
      omega
    · -- sum branch
      apply Finset.sum_congr rfl
      intro k hk
      -- after the split gives the needed inequalities, align the shifted coefficient index
      congr 1
      omega
```

The key point is to avoid trying to make `simp` solve the truncated-subtraction identity by itself. The equality of indices should be passed explicitly to congruence, and the natural-number side condition should be discharged by `omega`, e.g.

```lean
have hidx : n + 1 - k = n - (k - 1) := by
  omega
simpa [hidx]
```

or, when the goal is already under one function symbol,

```lean
congr 1
omega
```

For the finite-sum alignment, the expected skeleton is:

```lean
apply Finset.sum_congr rfl
intro k hk
-- use membership facts from `hk` and split hypotheses
congr 1
omega
```

## Blocker

To finish the requested code change, `scratch/FormalGroupW.lean` needs to exist on the remote `scratch` branch, or the exact file contents need to be provided in the conversation. Once that file is available through the connector, the proof should be patchable without changing surrounding definitions.
