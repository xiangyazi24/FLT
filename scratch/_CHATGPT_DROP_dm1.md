# Q1694 (dm1): debugging `(4*M)*(4*N)` vs `UV_eq_five_mul_fourth`

The working one-liner is:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  convert hUV using 1 <;> ring_nf [hM_val, hN_val]
```

That is the tactic you want.  Do **not** do `rw [hM_val, hN_val]; exact hUV`.  Force the comparison against `hUV`, and let `ring_nf` normalize every generated side goal using `hM_val` and `hN_val` as rewrite rules.

## Why `rw [hM_val, hN_val]; exact hUV` fails

Your theory is close in spirit but not quite the right mechanism.  The witness used to prove `h4U : 4 ∣ exprU` is not the important thing.  `Int.mul_ediv_cancel' h4U` produces an equality whose statement is determined by the expression in the type of `h4U`; the witness proof itself is not supposed to leak a different RHS.

The real issue is simpler: after `rw [hM_val, hN_val]`, Lean has an arithmetic expression that is mathematically the same as the LHS of `hUV`, but `exact hUV` requires the two proposition types to be **definitionally** the same.  `rw` does not canonicalize semiring expressions.  It just rewrites matching subterms.  If the resulting product has a different internal association/normal form from the one produced by `UV_eq_five_mul_fourth heq`, `exact` fails.

`ring_nf` is the canonicalizer.  But you should not first rewrite the goal and then try `exact hUV`; instead, use `convert` so Lean generates the equality-of-middle-expression side goals, then solve all of them by normalization:

```lean
convert hUV using 1 <;> ring_nf [hM_val, hN_val]
```

## Slightly more verbose version

If you want to see the generated bridge explicitly:

```lean
have h_prod_bridge :
    (4 * M) * (4 * N) =
      (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) *
      (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) := by
  ring_nf [hM_val, hN_val]

have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  exact h_prod_bridge.trans hUV
```

If `.trans hUV` still complains because `h_prod_bridge` and `hUV` use differently normalized versions of the middle expression, use the same forced-normalization idiom:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  convert hUV using 1 <;> ring_nf [hM_val, hN_val]
```

## Alternative destructive-normalization form

This also usually works, but it changes the local type of `hUV`:

```lean
have hUV' := hUV
ring_nf [hM_val, hN_val] at hUV' ⊢
exact hUV'
```

As a compact proof:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  have hUV' := hUV
  ring_nf [hM_val, hN_val] at hUV' ⊢
  exact hUV'
```

But the best one-liner is still:

```lean
have h : (4 * M) * (4 * N) = 5 * (4 * k) ^ 4 := by
  convert hUV using 1 <;> ring_nf [hM_val, hN_val]
```