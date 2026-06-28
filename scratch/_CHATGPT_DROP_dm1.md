# Q1620 (dm1): `set`, integer division, and the clean `16`-cancellation proof

The approach that works is: **do not try to rewrite the divided definitions of `M` and `N` inside `M * N`**. Keep the proof in the multiplied world.

You already have the essential bridge:

```lean
have h_prod_eq :
    (4 * M) * (4 * N) =
      (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) *
      (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) := by
  congr 1 <;> linarith
```

Then combine it with `hUV` by first proving the target after multiplying both sides by `16`, and only at the very end cancel `16`.

The proof is this shape:

```lean
have h16 :
    16 * (M * N) = 16 * (5 * (2 * k) ^ 4) := by
  calc
    16 * (M * N)
        = (4 * M) * (4 * N) := by
            ring
    _   = (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) *
          (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) :=
            h_prod_eq
    _   = 5 * (4 * k) ^ 4 :=
            hUV
    _   = 16 * (5 * (2 * k) ^ 4) := by
            ring

have hMN_2k : M * N = 5 * (2 * k) ^ 4 := by
  exact mul_left_cancel₀ (by norm_num : (16 : ℤ) ≠ 0) h16
```

If your local target is written with

```lean
set B₁ : ℤ := 2 * k with hB₁_def
```

then finish with:

```lean
have hMN_2k : M * N = 5 * (2 * k) ^ 4 := by
  exact mul_left_cancel₀ (by norm_num : (16 : ℤ) ≠ 0) h16

simpa [hB₁_def] using hMN_2k
```

If `B₁` is introduced by `let`/`set` with the equation in the opposite orientation, use the appropriate direction, for example:

```lean
simpa [hB₁_def] using hMN_2k
```

or, if needed,

```lean
simpa [hB₁_def.symm] using hMN_2k
```

but in the usual `set B₁ := 2 * k with hB₁_def` form, `simpa [hB₁_def]` is the one to try first.

## Why this avoids the `set` problem

The only place where `ring` sees `M` and `N` is the harmless identity

```lean
16 * (M * N) = (4 * M) * (4 * N)
```

That line is not supposed to extract information from the definitions of `M` and `N`; it is just arithmetic reassociation. Even if `ring` unfolds local definitions internally, the resulting proof still has exactly the equality needed for the `calc` chain.

The real information about the divisions is already packaged in

```lean
h_prod_eq : (4 * M) * (4 * N) = U * V
```

where `U` and `V` are the two undivided factors. After that, everything is pure integer arithmetic:

```lean
16 * (M * N)
= (4 * M) * (4 * N)
= U * V
= 5 * (4 * k) ^ 4
= 16 * (5 * (2 * k) ^ 4)
```

Then `mul_left_cancel₀` removes the common nonzero factor `16`.

## Slightly more robust version with local abbreviations

If the repeated expressions are making the goal unreadable, define `U` and `V` explicitly before the product bridge:

```lean
let U : ℤ := 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s
let V : ℤ := 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s

have h_prod_eq : (4 * M) * (4 * N) = U * V := by
  congr 1 <;> linarith

have h16 : 16 * (M * N) = 16 * (5 * (2 * k) ^ 4) := by
  calc
    16 * (M * N) = (4 * M) * (4 * N) := by
      ring
    _ = U * V := h_prod_eq
    _ = 5 * (4 * k) ^ 4 := hUV
    _ = 16 * (5 * (2 * k) ^ 4) := by
      ring

have hMN_2k : M * N = 5 * (2 * k) ^ 4 := by
  exact mul_left_cancel₀ (by norm_num : (16 : ℤ) ≠ 0) h16
```

This is the one stable pattern: **multiply, calc-chain through `(4*M)*(4*N)`, normalize the fourth powers, cancel the common factor**. No `ediv` reasoning is needed after `hM_val`/`hN_val` have been used to build `h_prod_eq`.
