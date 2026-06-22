# Q344-dm1: closing the `preΨ_invariant` coordinate-ring normalization steps

## The issue

The failing step is not algebraic; it is normalization.  Do **not** put the local definitions

```lean
mkC : R[X] →+* CoordinateRing := (mk W).comp C
q   : CoordinateRing := mk W W.ψ₂
```

in the simp set as `[mkC, q]`.  That unfolds them and leaves the normalized theorem in terms of `mk W (C f)` and `mk W W.ψ₂`, while the target and `hq4` are in terms of `mkC f` and `q`.

Instead, add two local **folding** lemmas:

```lean
have hmkC_apply (f : R[X]) : mk W (C f) = mkC f := rfl
have hq_apply : mk W W.ψ₂ = q := rfl
```

Then use those in `simp`.  This rewrites `mk W (C f)` to `mkC f` and `mk W W.ψ₂` to `q`, so the later `← hq4` rewrite sees exactly `mkC (W.Ψ₂Sq^2)`.

---

## Even branch: replacement for `hq_mul`

Use this block exactly in the even branch, after you have:

```lean
hm      : Even m
hm_p2   : Even (m + 2)
hm_m2   : Even (m - 2)
hm_p1   : ¬ Even (m + 1)
hm_m1   : ¬ Even (m - 1)
hMk     : mk W (C W.Ψ₃ *
              (W.ψ (m + 2) * W.ψ (m - 1)^2
                + W.ψ (m + 1)^2 * W.ψ (m - 2)
                + W.ψ₂^2 * W.ψ m^3))
            = mk W ((C W.preΨ₄ + W.ψ₂^4)
                * (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1)))
hq4     : q^4 = mkC (W.Ψ₂Sq^2)
```

The target is:

```lean
q * mkC (W.Ψ₃ * preΨInvN W m)
  = q * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m)
```

Tactic block:

```lean
  have hq_mul :
      q * mkC (W.Ψ₃ * preΨInvN W m)
        = q * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    -- Fold coordinate-ring constants back to the local names used by the goal.
    have hmkC_apply (f : R[X]) : mk W (C f) = mkC f := rfl
    have hq_apply : mk W W.ψ₂ = q := rfl

    -- Normalize the mapped Ward invariant into q/mkC form.
    have hMk' := hMk
    simp [
      FLT.EDS.mk_ψ_eq,
      hmkC_apply, hq_apply,
      hm, hm_p2, hm_m2, hm_p1, hm_m1
    ] at hMk'

    -- Compare the normalized hMk' with the desired q-multiplied statement.
    -- Use `← hq4` so `mkC (Ψ₂Sq^2)` is converted to `q^4`; then `ring_nf`
    -- sees the common leftover factor q on both sides.
    linear_combination (norm :=
      (simp [preΨInvN, preΨInvD, hm, hmkC_apply, hq_apply, ← hq4]; ring_nf)) hMk'
```

What this produces internally is exactly:

```text
hMk' :
mkC Ψ₃ *
  ((mkC preΨ(m+2) * q) * mkC preΨ(m-1)^2
   + mkC preΨ(m+1)^2 * (mkC preΨ(m-2) * q)
   + q^2 * (mkC preΨ(m) * q)^3)
=
(mkC preΨ₄ + q^4)
  * (mkC preΨ(m+1) * (mkC preΨ(m) * q) * mkC preΨ(m-1)).
```

After expanding `preΨInvN` in the even branch,

```text
preΨInvN W m
= preΨ(m+2)preΨ(m-1)^2
  + preΨ(m+1)^2preΨ(m-2)
  + Ψ₂Sq^2 preΨ(m)^3,
```

and rewriting `mkC(Ψ₂Sq^2)` as `q^4`, this is ring-identical to the target multiplied by `q`.

---

## Odd branch: replacement for `hq2_mul`

Use this block exactly in the odd branch, after you have:

```lean
hm      : ¬ Even m
hm_p2   : ¬ Even (m + 2)
hm_m2   : ¬ Even (m - 2)
hm_p1   : Even (m + 1)
hm_m1   : Even (m - 1)
hMk     : mk W (C W.Ψ₃ *
              (W.ψ (m + 2) * W.ψ (m - 1)^2
                + W.ψ (m + 1)^2 * W.ψ (m - 2)
                + W.ψ₂^2 * W.ψ m^3))
            = mk W ((C W.preΨ₄ + W.ψ₂^4)
                * (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1)))
hq4     : q^4 = mkC (W.Ψ₂Sq^2)
```

The target is:

```lean
q^2 * mkC (W.Ψ₃ * preΨInvN W m)
  = q^2 * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m)
```

Tactic block:

```lean
  have hq2_mul :
      q^2 * mkC (W.Ψ₃ * preΨInvN W m)
        = q^2 * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    -- Fold coordinate-ring constants back to the local names used by the goal.
    have hmkC_apply (f : R[X]) : mk W (C f) = mkC f := rfl
    have hq_apply : mk W W.ψ₂ = q := rfl

    -- Normalize the mapped Ward invariant into q/mkC form.
    have hMk' := hMk
    simp [
      FLT.EDS.mk_ψ_eq,
      hmkC_apply, hq_apply,
      hm, hm_p2, hm_m2, hm_p1, hm_m1
    ] at hMk'

    -- Odd branch: the common leftover factor is q^2.  Again rewrite
    -- `mkC (Ψ₂Sq^2)` backward to `q^4` before `ring_nf`.
    linear_combination (norm :=
      (simp [preΨInvN, preΨInvD, hm, hmkC_apply, hq_apply, ← hq4]; ring_nf)) hMk'
```

Internally this produces:

```text
hMk' :
mkC Ψ₃ *
  (mkC preΨ(m+2) * (mkC preΨ(m-1) * q)^2
   + (mkC preΨ(m+1) * q)^2 * mkC preΨ(m-2)
   + q^2 * mkC preΨ(m)^3)
=
(mkC preΨ₄ + q^4)
  * ((mkC preΨ(m+1) * q) * mkC preΨ(m) * (mkC preΨ(m-1) * q)).
```

Since in the odd branch

```text
preΨInvN W m
= preΨ(m+2)preΨ(m-1)^2
  + preΨ(m+1)^2preΨ(m-2)
  + preΨ(m)^3,
```

this is ring-identical to the target multiplied by `q^2`.

---

## If `simp` does not rewrite `mk W (W.ψ n)` under powers

If your local `mk_ψ_eq` is not tagged or not found under powers, use an explicit `simp only` variant.  This is noisier but more deterministic.

Even branch:

```lean
  have hq_mul :
      q * mkC (W.Ψ₃ * preΨInvN W m)
        = q * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    have hmkC_apply (f : R[X]) : mk W (C f) = mkC f := rfl
    have hq_apply : mk W W.ψ₂ = q := rfl
    have hMk' := hMk
    simp only [
      map_mul, map_add, map_pow,
      FLT.EDS.mk_ψ_eq,
      hmkC_apply, hq_apply,
      if_pos hm, if_pos hm_p2, if_pos hm_m2,
      if_neg hm_p1, if_neg hm_m1,
      one_mul, mul_one
    ] at hMk'
    linear_combination (norm :=
      (simp [preΨInvN, preΨInvD, hm, hmkC_apply, hq_apply, ← hq4]; ring_nf)) hMk'
```

Odd branch:

```lean
  have hq2_mul :
      q^2 * mkC (W.Ψ₃ * preΨInvN W m)
        = q^2 * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    have hmkC_apply (f : R[X]) : mk W (C f) = mkC f := rfl
    have hq_apply : mk W W.ψ₂ = q := rfl
    have hMk' := hMk
    simp only [
      map_mul, map_add, map_pow,
      FLT.EDS.mk_ψ_eq,
      hmkC_apply, hq_apply,
      if_neg hm, if_neg hm_p2, if_neg hm_m2,
      if_pos hm_p1, if_pos hm_m1,
      one_mul, mul_one
    ] at hMk'
    linear_combination (norm :=
      (simp [preΨInvN, preΨInvD, hm, hmkC_apply, hq_apply, ← hq4]; ring_nf)) hMk'
```

---

## Why `← hq4` and not `hq4`

The goal contains `mkC (W.Ψ₂Sq^2)` after `mkC.map_mul/map_add/map_pow` normalization.  The normalized `hMk'` contains `q^4`, coming from `mk W (W.ψ₂^4)`.  Rewriting with

```lean
← hq4
```

changes

```text
mkC (W.Ψ₂Sq^2)  ↦  q^4,
```

so both sides live in the same coordinate-ring polynomial language.  Rewriting in the other direction leaves the ψ-products with powers such as `q^2 * (P0*q)^3`, and `simp` will not reliably discover the needed `q^5 = q * mkC(Ψ₂Sq^2)` normalization before `ring_nf`.

---

## Drop-in location in the previous proof

In the previous `preΨ_invariant_even` proof, replace only this block:

```lean
  have hq_mul :
      q * mkC (W.Ψ₃ * preΨInvN W m)
        = q * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    linear_combination (norm :=
      (simp [mkC, q, preΨInvN, preΨInvD,
        FLT.EDS.mk_ψ_eq, hm, hm_p2, hm_m2, hm_p1, hm_m1,
        hq2, hq4]; ring_nf)) hMk
```

by the even block above.

In `preΨ_invariant_odd`, replace only the analogous `hq2_mul` block by the odd block above.  The following cancellation lines remain unchanged:

```lean
  have hmk_eq :
      mkC (W.Ψ₃ * preΨInvN W m)
        = mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) :=
    mul_left_cancel₀ hq_ne hq_mul       -- even branch

  have hmk_eq :
      mkC (W.Ψ₃ * preΨInvN W m)
        = mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) :=
    mul_left_cancel₀ hq2_ne hq2_mul     -- odd branch
```

For the even branch, the cancellation line uses `hq_ne`; for the odd branch, it uses `hq2_ne`.
