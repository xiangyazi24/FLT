# Q1636 (dm1): bridging `Eq.trans` failure from hidden middle-term mismatch

The answer is **option 5: use `show` to force the exact middle type**, then compose.

In the clean case, this is enough:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  exact
    (show (4 * M) * (4 * N) = exprU * exprV from by
      simpa only using h_prod_eq).trans hUV
```

Equivalently, split it into two lines:

```lean
have h_prod_eq' : (4 * M) * (4 * N) = exprU * exprV := by
  simpa only using h_prod_eq

have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  exact h_prod_eq'.trans hUV
```

This is the right API move because it tells Lean: “please regard the first equality as having exactly this displayed RHS.” After that, `.trans hUV` has no middle-expression ambiguity.

## If `simpa only using h_prod_eq` still does not close

If the mismatch is not merely definitional/simp-normalization but an arithmetic presentation issue, use `convert` under the same forced `show`:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  exact
    (show (4 * M) * (4 * N) = exprU * exprV from by
      convert h_prod_eq using 1 <;> ring).trans hUV
```

or, more readably:

```lean
have h_prod_eq' : (4 * M) * (4 * N) = exprU * exprV := by
  convert h_prod_eq using 1 <;> ring

have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  exact h_prod_eq'.trans hUV
```

That is the robust version. It uses `convert` to align the printed-but-not-identical RHS/LHS middle term, and `ring` discharges the arithmetic normalization side goals.

## `calc` version

For this kind of problem, I usually write the proof as a `calc`, because the middle expression is then visibly pinned:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  calc
    (4 * M) * (4 * N) = exprU * exprV := by
      convert h_prod_eq using 1 <;> ring
    _ = 5 * (4 * k) ^ 4 := hUV
```

If `simpa only using h_prod_eq` works in the first line, prefer it over `convert`; otherwise use the `convert ... <;> ring` version.

## What not to use

Do not use `exact_mod_cast`; there is no cast/coercion issue here. Do not expect raw `Eq.trans h_prod_eq hUV` to work when Lean sees the middle terms as different expressions. Also avoid `simp only [h_prod_eq, hUV]` for this; it is direction-sensitive and much less explicit.

The stable pattern is:

```lean
have h_prod_eq' : exact_middle = exprU * exprV := by
  convert h_prod_eq using 1 <;> ring

exact h_prod_eq'.trans hUV
```

or inline:

```lean
exact
  (show exact_middle = exprU * exprV from by
    convert h_prod_eq using 1 <;> ring).trans hUV
```

where in your case `exact_middle` is `(4 * M) * (4 * N)`.