# Q1501 (dm1): extracting `IsCoprime` from a product

For a product on the **left** side,

```lean
hcopI : IsCoprime F₁ F₂
hF₁eq : F₁ = 5 * G
⊢ IsCoprime G F₂
```

the robust one-liner is:

```lean
exact (show IsCoprime (5 * G) F₂ from hF₁eq ▸ hcopI).of_mul_left_right
```

For a product on the **right** side,

```lean
hcopI : IsCoprime F₁ F₂
hF₂eq : F₂ = 5 * G
⊢ IsCoprime F₁ G
```

the robust one-liner is:

```lean
exact (show IsCoprime F₁ (5 * G) from hF₂eq ▸ hcopI).of_mul_right_right
```

The `show ... from` wrapper is the important trick: it forces Lean to see the rewritten hypothesis in the exact product shape needed by the projection lemma.

Here is a minimal compilable block:

```lean
import Mathlib

section

variable {R : Type*} [CommSemiring R]
variable {F₁ F₂ G : R}

example (hcopI : IsCoprime F₁ F₂) (hF₁eq : F₁ = 5 * G) :
    IsCoprime G F₂ := by
  exact (show IsCoprime (5 * G) F₂ from hF₁eq ▸ hcopI).of_mul_left_right

example (hcopI : IsCoprime F₁ F₂) (hF₂eq : F₂ = 5 * G) :
    IsCoprime F₁ G := by
  exact (show IsCoprime F₁ (5 * G) from hF₂eq ▸ hcopI).of_mul_right_right

end
```

If your equality is reversed, use `.symm`:

```lean
exact (show IsCoprime (5 * G) F₂ from hF₁eq.symm ▸ hcopI).of_mul_left_right
```

for

```lean
hF₁eq : 5 * G = F₁
```

and

```lean
exact (show IsCoprime F₁ (5 * G) from hF₂eq.symm ▸ hcopI).of_mul_right_right
```

for

```lean
hF₂eq : 5 * G = F₂
```

Mnemonic:

```lean
.of_mul_left_left   -- from IsCoprime (a*b) c to IsCoprime a c
.of_mul_left_right  -- from IsCoprime (a*b) c to IsCoprime b c
.of_mul_right_left  -- from IsCoprime a (b*c) to IsCoprime a b
.of_mul_right_right -- from IsCoprime a (b*c) to IsCoprime a c
```

So for `5 * G`, use the `_right` version to keep `G`.