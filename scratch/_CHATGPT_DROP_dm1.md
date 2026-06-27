# Q1514 (dm1): reusing the quartic descent proof in the symmetric factor case

Use **option 1**: extract the 80-line descent argument into a lemma whose distinguished variables are parameters.

Do **not** try to justify this by saying the original equation

```lean
s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4
```

is symmetric. It is not symmetric in `r` and `B`. The symmetry you can exploit is only the formal one inside the **factor-pair descent lemma**: the main descent proof uses an identity of the shape

```lean
4 * r ^ 2 = (x ^ 2 - y ^ 2) ^ 2 + 4 * y ^ 4
```

so the symmetric branch is the same lemma with `x := b` and `y := a`.

Also, `swap` is the wrong tool: it only swaps Lean goals. `this.symm` only reverses an equality. Neither one performs the variable swap `a ↔ b` through an 80-line proof script.

The intended abstraction is:

```lean
import Mathlib

-- Schematic statement: include exactly the positivity, gcd/coprimality,
-- factor-splitting, and smaller-solution hypotheses your 80-line proof uses.
-- The important point is that the proof is parameterized by `x y`, and the
-- fourth-power term is the second parameter `y`.
lemma descent_from_factor_pair
    {r B s x y : ℤ}
    -- examples of side conditions; replace by your actual ones
    (hxyB : x * y = B)
    (hid : 4 * r ^ 2 = (x ^ 2 - y ^ 2) ^ 2 + 4 * y ^ 4)
    -- plus the remaining side conditions from the main case
    : False := by
  -- Paste the already-proved main-case proof here once,
  -- replacing the old `a` by `x` and the old `b` by `y`.
  -- The descent then always goes through `y`.
  sorry
```

Then the symmetric branch should close by instantiating the lemma with the variables swapped:

```lean
import Mathlib

-- In the symmetric branch you have the identity
--   hsym_id : 4 * r^2 = (b^2-a^2)^2 + 4*a^4
-- and, typically, the same product/coprime side conditions with `a,b` swapped.

exact descent_from_factor_pair
  (r := r) (B := B) (s := s)
  (x := b) (y := a)
  (by simpa [mul_comm] using habB)
  hsym_id
```

If the extracted lemma still uses binder names `a b` rather than `x y`, the same idea is:

```lean
import Mathlib

exact descent_from_factor_pair
  (r := r) (B := B) (s := s)
  (a := b) (b := a)
  (by simpa [mul_comm] using habB)
  hsym_id
```

For extra side conditions, add them in the same swapped order. Typical conversions are:

```lean
import Mathlib

refine descent_from_factor_pair
  (r := r) (B := B) (s := s)
  (x := b) (y := a)
  ?hbaB ?hid ?more_side_conditions

-- product condition, if the available hypothesis is `habB : a * b = B`
· simpa [mul_comm] using habB

-- the identity usually needs no algebra: after `x := b`, `y := a`,
-- the lemma asks exactly for `(b^2-a^2)^2 + 4*a^4`.
· exact hsym_id

-- if one of your side conditions is symmetric, use its `.symm` lemma if it has one;
-- otherwise `simpa [mul_comm]` or `ring_nf` usually handles the bookkeeping.
```

If your current “main case proof” is only a local branch proof like

```lean
have hmain : False := by
  -- 80 lines specialized to the current `a b`
  ...
```

then there is no one-liner that replays it with `a` and `b` swapped. Lean cannot alpha-rename a finished proof script into a new proof state. You must either extract it into a lemma/local function as above, or copy the proof. The clean Lean version is therefore:

```lean
import Mathlib

-- Main branch
exact descent_from_factor_pair (x := a) (y := b) habB hmain_id

-- Symmetric branch
exact descent_from_factor_pair (x := b) (y := a) (by simpa [mul_comm] using habB) hsym_id
```

So the answer is: **extract `descent_from_factor_pair`; close the symmetric case by calling it with `(x,y) = (b,a)`.** Copying is only a stopgap, and `swap`/`this.symm` is not the right abstraction.
