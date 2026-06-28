# Q1572 (dm2/dm4): architecture for sharing the odd/even quartic descent

## Verdict

Yes, this is worth refactoring, but **not with the exact `descent_from_coprime_pair` signature proposed in the question**.

Do **not** duplicate the full 130-line descent chain permanently.  The right split is:

1. Keep the odd/even normalization code as thin branch-specific wrappers.
2. Extract the genuinely common proof only after the branch has produced an **oriented fourth-power split** and the exact algebraic identity used by the descent.
3. Make the extracted core return a descent measured against the normalized parameter `C`, not directly against the original branch parameter `B`.

So the core should prove roughly:

```lean
B'.natAbs < C.natAbs
```

Then the wrappers finish the case-specific bound:

```lean
-- odd branch: C = B
B'.natAbs < B.natAbs

-- even branch: C = B₁ and B₁ < B
B'.natAbs < B₁.natAbs < B.natAbs
```

This avoids threading `B`, `B₁`, `/4`, and divisibility facts through the common 100-line payload.

## Why the proposed boundary is too high-level

The proposed theorem starts with:

```lean
private theorem descent_from_coprime_pair {r B s F₁ F₂ C : ℤ}
    ...
    (hF_prod : F₁ * F₂ = 5 * C ^ 4)
    (hF_cop : Int.gcd F₁ F₂ = 1)
    ...
    (hC_dvd_B : C ∣ B)
    (hsum : F₁ + F₂ = 4 * r ^ 2 + 2 * C ^ 2)
    ...
```

This mixes three different layers:

1. original quartic data: `r B s`, `heq`, `hr_odd`, `hnonbase`;
2. normalized factor-pair data: `F₁ F₂ C`, product, gcd, positivity;
3. post-split descent data: `a b`, the `h4r2` identity, `h`, `r² = h² + b⁴`, and the new smaller solution.

That makes the theorem brittle.  In particular, the `hsum` hypothesis is not stable across the odd/even normalization.

For the odd raw pair

```lean
U = 2 * r ^ 2 + B ^ 2 - 2 * s
V = 2 * r ^ 2 + B ^ 2 + 2 * s
C = B
```

you naturally get

```lean
U + V = 4 * r ^ 2 + 2 * C ^ 2
U * V = 5 * C ^ 4
```

But for the even normalized pair

```lean
M = U / 4
N = V / 4
C = B₁        -- usually B = 2 * B₁, or stronger divisibility upstream
```

the sum is typically

```lean
M + N = r ^ 2 + 2 * C ^ 2
```

not

```lean
M + N = 4 * r ^ 2 + 2 * C ^ 2.
```

So if the shared theorem assumes `F₁ + F₂ = 4*r^2 + 2*C^2`, it is secretly an odd-branch theorem.  If the even branch really has the same later identity

```lean
4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

then pass **that identity directly** to the shared core.  Do not force both branches through the same `hsum` statement.

## Recommended extraction boundary

Extract the proof after `coprime_factor_5_fourth` has produced an oriented split and after the branch-specific algebra has produced the descent identity.

The common core should look like this, modulo the exact names already in the file:

```lean
import Mathlib

namespace FLT.DM4

/--
The actual branch-free descent payload.

This theorem should contain the long shared chain:

* define `h`, usually from `(a^2 - b^2) / 2`;
* prove `r^2 = h^2 + b^4`;
* prove the needed coprimality, e.g. `coprime_rh`;
* apply the positive fourth-power/Pythagorean step;
* build the new `QuarticPlusZ` solution;
* prove the new solution is non-base;
* prove the new measure is smaller than `C`.

It should not know whether `C` came from `B` or from `B/2`.
-/
private theorem descent_from_oriented_h4r2
    {r C a b : ℤ}
    (hr : 0 < r)
    (hC : 0 < C)
    (hcop_rC : Int.gcd r C = 1)
    (ha : 0 < a)
    (hb : 0 < b)
    (hC_eq : C = a * b)
    (hab_cop : Int.gcd a b = 1)
    (h4r2 : 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4)
    -- Use the exact minimal non-base/size hypothesis the shared proof really needs.
    -- Prefer `1 < C.natAbs` or `¬ BaseZ r C` over the original `¬ BaseZ r B`.
    (hnonbaseC : ¬ BaseZ r C) :
    ∃ r' B' s',
      QuarticPlusZ r' B' s' ∧
      ¬ BaseZ r' B' ∧
      B'.natAbs < C.natAbs := by
  -- Move the existing shared 100-ish lines here.
  -- This theorem should start exactly where the odd/even proofs become textually identical.
  sorry

end FLT.DM4
```

The exact `hnonbaseC` hypothesis may be too strong or too weak depending on your current definitions.  The important rule is: **pass the precise thing the common proof needs**, not the original branch-level `hnonbase : ¬ BaseZ r B` unless the common proof literally uses that exact statement.

Very often the right replacement is one of:

```lean
( hC_gt_one : 1 < C.natAbs )
```

or

```lean
( hb_gt_one : 1 < b.natAbs )
```

because the descent usually only needs to rule out the trivial/base split.

## Thin odd wrapper

The odd branch should do only the raw factor construction, factor split, orientation, and bound rewrite.

Skeleton:

```lean
private theorem odd_branch_descent
    {r B s : ℤ}
    (hr : 0 < r)
    (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hnonbase : ¬ BaseZ r B)
    -- plus whatever parity/positivity hypotheses this branch needs
    : ∃ r' B' s',
      QuarticPlusZ r' B' s' ∧
      ¬ BaseZ r' B' ∧
      B'.natAbs < B.natAbs := by
  let U : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
  let V : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

  have hUV_prod : U * V = 5 * B ^ 4 := by
    -- branch-specific algebra from `heq`
    sorry

  have hUV_cop : Int.gcd U V = 1 := by
    -- existing odd gcd proof
    sorry

  have hUV_pos : 0 < U ∧ 0 < V := by
    -- existing positivity proof
    sorry

  have hUV_sum : U + V = 4 * r ^ 2 + 2 * B ^ 2 := by
    dsimp [U, V]
    ring

  -- Run the existing fourth-power splitting lemma here.
  -- The exact return shape depends on your current `coprime_factor_5_fourth`.
  rcases coprime_factor_5_fourth hUV_prod hUV_cop hUV_pos with
    | inl hsplit =>
        rcases hsplit with ⟨a, b, ha, hb, hB_eq, hU, hV, hab_cop⟩
        have h4r2 : 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
          -- This is the odd branch algebra:
          -- use hUV_sum, hU, hV, and hB_eq.
          -- From U+V = a^4 + 5*b^4 and B = a*b,
          -- get 4*r^2 = (a^2-b^2)^2 + 4*b^4.
          nlinarith [hUV_sum]
        simpa [hB_eq] using
          descent_from_oriented_h4r2
            (r := r) (C := B) (a := a) (b := b)
            hr hB hcop ha hb hB_eq hab_cop h4r2 hnonbase
    | inr hsplit =>
        -- Same call after swapping the orientation names.
        sorry
```

The branch-specific part is allowed to be 20--40 lines.  That is fine.  The important thing is that the post-`h4r2` descent does not appear twice.

## Thin even wrapper

The even branch should normalize first, prove the pair facts for `M,N,C`, then call the same core with `C = B₁`.

Skeleton:

```lean
private theorem even_branch_descent
    {r B s B₁ : ℤ}
    (hr : 0 < r)
    (hB : 0 < B)
    (hB_eq : B = 2 * B₁)
    (hB₁_pos : 0 < B₁)
    (hB₁_lt_B : B₁.natAbs < B.natAbs)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hnonbase_for_core : ¬ BaseZ r B₁)
    -- plus the divisibility hypotheses giving U/4 and V/4
    : ∃ r' B' s',
      QuarticPlusZ r' B' s' ∧
      ¬ BaseZ r' B' ∧
      B'.natAbs < B.natAbs := by
  let U : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
  let V : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s
  let M : ℤ := U / 4
  let N : ℤ := V / 4

  have hMN_prod : M * N = 5 * B₁ ^ 4 := by
    -- branch-specific `/4` algebra
    sorry

  have hMN_cop : Int.gcd M N = 1 := by
    -- normalized gcd proof
    sorry

  have hMN_pos : 0 < M ∧ 0 < N := by
    -- positivity after division by 4
    sorry

  have hcop_rB₁ : Int.gcd r B₁ = 1 := by
    -- derive from hcop and B = 2*B₁, or from the exact available lemma
    sorry

  rcases coprime_factor_5_fourth hMN_prod hMN_cop hMN_pos with
    | inl hsplit =>
        rcases hsplit with ⟨a, b, ha, hb, hB₁_eq, hM, hN, hab_cop⟩
        have h4r2 : 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
          -- Do the even-specific algebra here.
          -- Important: do not assume the odd raw sum identity unless it is actually true
          -- for M,N,B₁.  If the normalized sum is different, prove h4r2 by the
          -- even branch's real algebra, or move the shared core later.
          sorry
        rcases descent_from_oriented_h4r2
            (r := r) (C := B₁) (a := a) (b := b)
            hr hB₁_pos hcop_rB₁ ha hb hB₁_eq hab_cop h4r2 hnonbase_for_core with
          ⟨r', B', s', hQ, hnon, hltB₁⟩
        exact ⟨r', B', s', hQ, hnon, lt_trans hltB₁ hB₁_lt_B⟩
    | inr hsplit =>
        -- Same call after swapping the orientation names.
        sorry
```

This is the cleanest way to handle the different final bound:

```lean
-- core gives
hltB₁ : B'.natAbs < B₁.natAbs

-- wrapper adds
hB₁_lt_B : B₁.natAbs < B.natAbs

-- final
lt_trans hltB₁ hB₁_lt_B
```

## If the even identity is not literally `h4r2`

Double-check this before extracting.

For `U,V` raw, the odd-style sum is:

```lean
U + V = 4 * r ^ 2 + 2 * B ^ 2
```

For `M = U/4`, `N = V/4`, and `B = 2*B₁`, the normalized sum is:

```lean
M + N = r ^ 2 + 2 * B₁ ^ 2
```

So after splitting

```lean
M = a ^ 4,
N = 5 * b ^ 4,
B₁ = a * b,
```

the immediate algebra gives a different-looking identity from the odd raw case.  If your current even proof still reaches exactly

```lean
4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

then put that even-specific derivation in the wrapper and share from there.

If instead the even branch reaches a different identity, then move the extraction boundary later: start the shared theorem at the first statement that is literally identical in both branches, for example after you have already proved

```lean
r ^ 2 = h ^ 2 + b ^ 4
```

or after whatever normalized `h` identity the two branches truly share.

The rule is:

> The shared theorem should start at the first line where the two proofs are textually the same after renaming variables.

Do not force both branches through a fake common `hsum`.

## Practical recommendation

Use this three-layer architecture:

```lean
-- Layer 1: branch-specific normalization
odd_branch_descent
  -- constructs U,V,C=B and proves pair facts

even_branch_descent
  -- constructs M,N,C=B₁ and proves pair facts

-- Layer 2: branch-specific orientation/algebra
-- calls coprime_factor_5_fourth and proves h4r2, or whatever is the true common identity

-- Layer 3: branch-free descent core
descent_from_oriented_h4r2
  -- long shared chain; returns B'.natAbs < C.natAbs
```

This is worth the refactor because the repeated part is not 10 lines of algebra; it is the fragile descent chain involving coprimality, positivity, fourth powers, construction of the next solution, non-base, and the measure decrease.  Duplicating that means every later fix must be made twice.

But keep the abstraction **low enough**:

* do not pass `s` unless the common core uses `s`;
* do not pass `heq` unless the common core uses the original quartic equation;
* do not pass `hr_odd` unless the common core uses parity of `r`;
* do not pass `hC_dvd_B`; instead derive and pass `Int.gcd r C = 1`;
* do not pass a branch-specific `hsum`; pass the already-proved common identity;
* make the core measure decrease be `< C.natAbs`, then let wrappers translate it to `< B.natAbs`.

Temporary duplication is fine as a workflow if the even branch is not green yet: copy the odd proof, make the even proof compile, then extract the literal common suffix.  But the final architecture should not keep two 130-line copies.
