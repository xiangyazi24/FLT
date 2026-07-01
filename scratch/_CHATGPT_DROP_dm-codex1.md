# Q2728 (dm-codex1): bridge from `EisensteinTriplePrimitiveParamOrUnit` to `NormalizedBadParamStatement`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local worktree from prompt: `/Users/huangx/repos/flt-ai`  
Target file: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean` or a small downstream file

## Scope

This bridge does **not** reprove the primitive Eisenstein triple parametrization. It assumes the supplied theorem/axiom-like input

```lean
theorem normalizedBadParamStatement_of_tripleParamOrUnit
    (hTriple : EisensteinTriplePrimitiveParamOrUnit) :
    NormalizedBadParamStatement := by
  ...
```

The only work is:

1. turn `NormalizedEisensteinBad A N S` into a primitive positive Eisenstein triple on `(A^2, N^2, S)`;
2. apply `hTriple`;
3. kill the unit branch using `0 < A`, `A < N`;
4. unpack `EisensteinFullParam (A^2) (N^2) S m n` into one of the four branch disjuncts.

The raw-sector hypothesis `¬ (3 : ℤ) ∣ m+n` is intentionally ignored because `EisensteinSqBranch` does not require it. The divided-sector hypothesis `(3 : ℤ) ∣ m+n` is exactly the fourth field of `DividedSquareBranch`.

If you paste this into `N12QuarticEisenstein.lean` itself, remove the import. If you put it in a downstream file, keep the import.

## Lean code skeleton

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Positive integer with square equal to `1` is `1`.

Mathlib usually has `sq_eq_one_iff`. If this theorem has a slightly different
name in your local snapshot, replace only the two lines producing `hcases`; the
rest of the bridge is independent of that API. -/
private lemma int_eq_one_of_pos_sq_eq_one {a : ℤ}
    (ha : 0 < a) (h : a ^ 2 = 1) :
    a = 1 := by
  have hcases : a = 1 ∨ a = -1 := by
    exact sq_eq_one_iff.mp h
  rcases hcases with h1 | hm1
  · exact h1
  · exfalso
    have : (0 : ℤ) < -1 := by
      simpa [hm1] using ha
    norm_num at this

/-- Positivity of a square from positivity of the base. -/
private lemma int_sq_pos_of_pos {a : ℤ} (ha : 0 < a) :
    0 < a ^ 2 := by
  exact sq_pos_of_ne_zero (ne_of_gt ha)

/-- Robust fallback proof that coprimality survives squaring on both sides.

If your local Mathlib has the API, the whole proof can be replaced by either

```lean
  simpa using h.pow 2 2
```

or

```lean
  simpa using (h.pow_left 2).pow_right 2
```

The Bezout/cubic proof below avoids relying on the exact method name. It assumes
Mathlib's usual `IsCoprime` witness shape `∃ u v, u * a + v * b = 1`. If your
local pretty-printer reveals the commuted witness `a * u + b * v = 1`, the same
proof works after `simpa [mul_comm, mul_left_comm, mul_assoc] using huv` or after
commuting the two products in the `calc`. -/
private lemma isCoprime_sq_sq_int {a b : ℤ}
    (h : IsCoprime a b) :
    IsCoprime (a ^ 2) (b ^ 2) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u ^ 3 * a + 3 * u ^ 2 * v * b,
          3 * u * v ^ 2 * a + v ^ 3 * b, ?_⟩
  calc
    (u ^ 3 * a + 3 * u ^ 2 * v * b) * (a ^ 2) +
        (3 * u * v ^ 2 * a + v ^ 3 * b) * (b ^ 2)
        = (u * a + v * b) ^ 3 := by
          ring
    _ = (1 : ℤ) := by
          rw [huv]
          norm_num

/-- Raw, first orientation:
`X = m^2-n^2`, `Y = 2mn-n^2` becomes `EisensteinSqBranch A N S m n`
when `X=A^2`, `Y=N^2`. -/
private lemma sqBranch_of_rawParam_left
    {A N S m n : ℤ}
    (hnpos : 0 < n) (hnm : n < m) (hmn : IsCoprime m n)
    (hZ : S = m ^ 2 - m * n + n ^ 2)
    (hX : A ^ 2 = m ^ 2 - n ^ 2)
    (hY : N ^ 2 = 2 * m * n - n ^ 2) :
    EisensteinSqBranch A N S m n := by
  refine ⟨hnpos, hnm, hmn, ?_, ?_, hZ⟩
  · calc
      A ^ 2 = m ^ 2 - n ^ 2 := hX
      _ = (m - n) * (m + n) := by ring
  · calc
      N ^ 2 = 2 * m * n - n ^ 2 := hY
      _ = n * (2 * m - n) := by ring

/-- Divided, first orientation:
`3*X = m^2-n^2`, `3*Y = 2mn-n^2` becomes
`DividedSquareBranch A N S m n` when `X=A^2`, `Y=N^2`. -/
private lemma dividedBranch_of_dividedParam_left
    {A N S m n : ℤ}
    (hnpos : 0 < n) (hnm : n < m) (hmn : IsCoprime m n)
    (h3 : (3 : ℤ) ∣ m + n)
    (hZ : 3 * S = m ^ 2 - m * n + n ^ 2)
    (hX : 3 * A ^ 2 = m ^ 2 - n ^ 2)
    (hY : 3 * N ^ 2 = 2 * m * n - n ^ 2) :
    DividedSquareBranch A N S m n := by
  refine ⟨hnpos, hnm, hmn, h3, ?_, ?_, hZ⟩
  · calc
      3 * A ^ 2 = m ^ 2 - n ^ 2 := hX
      _ = (m - n) * (m + n) := by ring
  · calc
      3 * N ^ 2 = 2 * m * n - n ^ 2 := hY
      _ = n * (2 * m - n) := by ring

/-- Main bridge. -/
theorem normalizedBadParamStatement_of_tripleParamOrUnit
    (hTriple : EisensteinTriplePrimitiveParamOrUnit) :
    NormalizedBadParamStatement := by
  intro A N S hbad

  -- Unpack the normalized bad data.
  rcases hbad with ⟨hApos, hAltN, hSpos, hcopAN, hquartic⟩
  have hNpos : 0 < N := lt_trans hApos hAltN

  -- Positivity of the square sides.
  have hA2pos : 0 < A ^ 2 := int_sq_pos_of_pos hApos
  have hN2pos : 0 < N ^ 2 := int_sq_pos_of_pos hNpos

  -- Primitive square sides.
  have hcopSq : IsCoprime (A ^ 2) (N ^ 2) :=
    isCoprime_sq_sq_int hcopAN

  -- Quartic bad equation is exactly an Eisenstein triple on square sides.
  have htri : EisensteinTriple (A ^ 2) (N ^ 2) S :=
    eisensteinTriple_of_quartic hquartic

  -- Apply the primitive triple parametrization theorem.
  have hparamOrUnit : EisensteinTripleParamOrUnit (A ^ 2) (N ^ 2) S :=
    hTriple hA2pos hN2pos hSpos hcopSq htri

  rcases hparamOrUnit with hunit | hparam
  · -- Unit branch: `A^2=1`, `N^2=1`, `S=1`, contradicting `A<N`
    -- because `A,N` are positive.
    rcases hunit with ⟨hA2eq, hN2eq, _hSeq⟩
    have hAeq : A = 1 := int_eq_one_of_pos_sq_eq_one hApos hA2eq
    have hNeq : N = 1 := int_eq_one_of_pos_sq_eq_one hNpos hN2eq
    exfalso
    have : (1 : ℤ) < 1 := by
      simpa [hAeq, hNeq] using hAltN
    exact (lt_irrefl (1 : ℤ)) this

  · -- Non-unit parametrized branch.
    rcases hparam with ⟨m, n, hfull⟩
    refine ⟨m, n, ?_⟩
    rcases hfull with ⟨hnpos, hnm, hmn, hcases⟩

    rcases hcases with hraw | hdiv
    · -- Raw sector.
      rcases hraw with ⟨_hnot3, hp⟩
      rcases hp with ⟨hZ, horient⟩
      rcases horient with hleft | hright
      · -- `A^2 = m^2-n^2`, `N^2 = 2mn-n^2`.
        rcases hleft with ⟨hX, hY⟩
        exact Or.inl
          (sqBranch_of_rawParam_left hnpos hnm hmn hZ hX hY)
      · -- Swapped raw orientation:
        -- `N^2 = m^2-n^2`, `A^2 = 2mn-n^2`.
        rcases hright with ⟨hYdiff, hXother⟩
        exact Or.inr <| Or.inl
          (sqBranch_of_rawParam_left (A := N) (N := A) (S := S)
            hnpos hnm hmn hZ hYdiff hXother)

    · -- Divided-by-3 sector.
      rcases hdiv with ⟨h3, hZ3, horient⟩
      rcases horient with hleft | hright
      · -- `3*A^2 = m^2-n^2`, `3*N^2 = 2mn-n^2`.
        rcases hleft with ⟨hX3, hY3⟩
        exact Or.inr <| Or.inr <| Or.inl
          (dividedBranch_of_dividedParam_left hnpos hnm hmn h3 hZ3 hX3 hY3)
      · -- Swapped divided orientation:
        -- `3*N^2 = m^2-n^2`, `3*A^2 = 2mn-n^2`.
        rcases hright with ⟨hY3diff, hX3other⟩
        exact Or.inr <| Or.inr <| Or.inr
          (dividedBranch_of_dividedParam_left (A := N) (N := A) (S := S)
            hnpos hnm hmn h3 hZ3 hY3diff hX3other)
```

## Notes on likely local fixes

### 1. `IsCoprime` API alternative

If the fallback Bezout proof does not match the local internal definition of `IsCoprime`, replace the body of `isCoprime_sq_sq_int` with the Mathlib API. The most likely working versions are:

```lean
private lemma isCoprime_sq_sq_int {a b : ℤ}
    (h : IsCoprime a b) :
    IsCoprime (a ^ 2) (b ^ 2) := by
  simpa using h.pow 2 2
```

or

```lean
private lemma isCoprime_sq_sq_int {a b : ℤ}
    (h : IsCoprime a b) :
    IsCoprime (a ^ 2) (b ^ 2) := by
  simpa using (h.pow_left 2).pow_right 2
```

### 2. `sq_eq_one_iff` alternative

If `sq_eq_one_iff` is not in scope, search for one of these common names:

```lean
#check sq_eq_one_iff
#check sq_eq_one_iff_eq_or_eq_neg
#check Int.sq_eq_one_iff
```

The needed lemma shape is only:

```lean
∀ {a : ℤ}, a ^ 2 = 1 → a = 1 ∨ a = -1
```

### 3. Why no `A±N` shortcuts appear

The bridge does not factor `A+N` or `A-N`. It only translates the already-provided parametrization of the primitive Eisenstein triple. The only factorization identities used are the safe polynomial identities

```lean
m ^ 2 - n ^ 2 = (m - n) * (m + n)
2 * m * n - n ^ 2 = n * (2 * m - n)
```

both discharged by `ring`.

### 4. Branch orientation map

For `EisensteinFullParam (A^2) (N^2) S m n`:

```text
raw left:
  A^2 = m^2-n^2, N^2 = 2mn-n^2
  ↦ EisensteinSqBranch A N S m n

raw right:
  N^2 = m^2-n^2, A^2 = 2mn-n^2
  ↦ EisensteinSqBranch N A S m n

divided left:
  3*A^2 = m^2-n^2, 3*N^2 = 2mn-n^2
  ↦ DividedSquareBranch A N S m n

divided right:
  3*N^2 = m^2-n^2, 3*A^2 = 2mn-n^2
  ↦ DividedSquareBranch N A S m n
```

That is exactly the four-way disjunction in `NormalizedBadParamStatement`.
