# Q1337 (dm1/dm2): tactics for the `s^2` and `-s^2` subcases

I did not find a local `quartic_plus` declaration in the repository search index, so below I write the branch code in a form you can paste into your local proof. Replace the one line

```lean
  have hbase := quartic_plus (|r|) B s hr_pos hBpos hgcd_rB hquartic
```

by your exact local `quartic_plus` call if its argument order differs.

Throughout, set the second factor once:

```lean
let F : ℤ := A ^ 2 + A * B ^ 2 - B ^ 4
```

and suppose the split produced

```lean
rcases hs_split with ⟨s, hFsq | hFneg_sq⟩
```

where `hFsq : F = s ^ 2` and `hFneg_sq : F = -s ^ 2`.

## Positive square branch

This is the branch `F = s^2`.

```lean
  -- hFsq : F = s ^ 2
  have habs2 : |r| ^ 2 = r ^ 2 := by
    simpa [pow_two] using sq_abs r

  have hquartic :
      s ^ 2 = |r| ^ 4 + |r| ^ 2 * B ^ 2 - B ^ 4 := by
    -- `F = s^2`, `A = r^2`, and `|r|^2 = r^2`.
    rw [← hFsq]
    dsimp [F]
    rw [hrpos]
    rw [← habs2]
    ring

  -- Adjust this line if your local theorem has a different argument order.
  have hbase := quartic_plus (|r|) B s hr_pos hBpos hgcd_rB hquartic
  rcases hbase with ⟨hr_abs_one, hB_one⟩

  have hA_one : A = 1 := by
    rw [hrpos]
    rw [← habs2, hr_abs_one]
    norm_num

  -- If your goal is `u = 1` and you have `hu : u = (A : ℚ) / (B : ℚ)^2`:
  have hu_one : u = 1 := by
    rw [hu, hA_one, hB_one]
    norm_num
```

If your `quartic_plus` theorem is Nat-valued, bridge by applying it to `r.natAbs` and `B.natAbs`; the equation is the same after `norm_num`/`exact_mod_cast` because `0 < B` gives `B.natAbs = B` as an integer cast and `|r|` is `r.natAbs` on the nonnegative side.

## Negative square branch

This is the branch `F = -s^2`. The following is the clean contradiction. It needs `hF_ne : F ≠ 0`; if you do not already have it, prove it just before this branch from your coprimality/primitive hypotheses.

```lean
  -- hFneg_sq : F = -s ^ 2
  have hr_ne : r ≠ 0 := by
    intro hr0
    have : |r| = 0 := by simp [hr0]
    linarith

  have hApos : 0 < A := by
    rw [hrpos]
    exact sq_pos_of_ne_zero hr_ne

  have hs_ne : s ≠ 0 := by
    intro hs0
    apply hF_ne
    rw [hFneg_sq, hs0]
    ring

  have hFneg : F < 0 := by
    rw [hFneg_sq]
    exact neg_neg_of_pos (sq_pos_of_ne_zero hs_ne)

  have hprodneg : A * F < 0 :=
    mul_neg_of_pos_of_neg hApos hFneg

  have hCnonneg : 0 ≤ C ^ 2 := sq_nonneg C

  have hClt : C ^ 2 < 0 := by
    rw [hC]
    exact hprodneg

  exact (not_lt_of_ge hCnonneg) hClt
```

If you did not name `F`, replace every `F` above by

```lean
A ^ 2 + A * B ^ 2 - B ^ 4
```

but naming it makes both branches much easier for `rw`, `dsimp`, and `ring`.
