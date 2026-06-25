# Q43 (dm1): corrected rank-3 apparition repair

This is the surgical repair for the eight remaining errors in
`preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero`.

The key change is to **normalize the even and odd recursive indices to the
integer forms used by Mathlib's `preΨ_even` / `preΨ_odd`** before passing them to
hypotheses:

```lean
((M + M : ℕ) : ℤ)       = 2 * (M : ℤ)
((M + M + 1 : ℕ) : ℤ)   = 2 * (M : ℤ) + 1
```

and to avoid the ambiguous `three_dvd_two_mul_iff.mp ?_` placeholder in the
`M % 3 = 0` branch.  In that branch the proof should use the modular hypothesis
itself, not try to synthesize a hidden divisibility proof from a cast-rewritten
polynomial equality.

The two odd-branch nonzero goals are closed by reducing the recurrence to either
`0 - B` or `A - 0`, proving the surviving factor is nonzero by `mul_ne_zero`,
`pow_ne_zero`, and the hypothesis `hs2 : sx W x ≠ 0`.

---

## Helper block

Paste this near the other local arithmetic helpers.  These names are deliberately
`q43_...` so they do not collide with your existing helpers.

```lean
private lemma q43_natCast_add_self (M : ℕ) :
    ((M + M : ℕ) : ℤ) = 2 * (M : ℤ) := by
  omega

private lemma q43_natCast_add_self_add_one (M : ℕ) :
    ((M + M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 := by
  omega

private lemma q43_natCast_sub_one {M : ℕ} (hM : 1 ≤ M) :
    (((M - 1 : ℕ) : ℤ)) = (M : ℤ) - 1 := by
  omega

private lemma q43_natCast_sub_two {M : ℕ} (hM : 2 ≤ M) :
    (((M - 2 : ℕ) : ℤ)) = (M : ℤ) - 2 := by
  omega

private lemma q43_natCast_add_one (M : ℕ) :
    (((M + 1 : ℕ) : ℤ)) = (M : ℤ) + 1 := by
  omega

private lemma q43_natCast_add_two (M : ℕ) :
    (((M + 2 : ℕ) : ℤ)) = (M : ℤ) + 2 := by
  omega

private lemma q43_three_dvd_two_mul_iff (M : ℕ) :
    3 ∣ 2 * M ↔ 3 ∣ M := by
  omega

private lemma q43_three_dvd_add_self_iff (M : ℕ) :
    3 ∣ M + M ↔ 3 ∣ M := by
  omega

private lemma q43_three_dvd_add_self_add_one_iff (M : ℕ) :
    3 ∣ M + M + 1 ↔ M % 3 = 1 := by
  omega

private lemma q43_not_three_dvd_add_self_of_mod_one {M : ℕ}
    (hM : M % 3 = 1) :
    ¬ 3 ∣ M + M := by
  omega

private lemma q43_not_three_dvd_add_self_of_mod_two {M : ℕ}
    (hM : M % 3 = 2) :
    ¬ 3 ∣ M + M := by
  omega

private lemma q43_not_three_dvd_add_self_add_one_of_mod_zero {M : ℕ}
    (hM : M % 3 = 0) :
    ¬ 3 ∣ M + M + 1 := by
  omega

private lemma q43_not_three_dvd_add_self_add_one_of_mod_two {M : ℕ}
    (hM : M % 3 = 2) :
    ¬ 3 ∣ M + M + 1 := by
  omega

private lemma q43_ite_even_sx_sq_ne_zero {k : Type*} [Semiring k] [NoZeroDivisors k]
    {s : k} (hs : s ≠ 0) (m : ℤ) :
    (if Even m then s ^ 2 else 1) ≠ 0 := by
  by_cases hm : Even m
  · simp [hm, pow_ne_zero 2 hs]
  · simp [hm]

private lemma q43_ite_even_one_or_sx_sq_ne_zero {k : Type*} [Semiring k] [NoZeroDivisors k]
    {s : k} (hs : s ≠ 0) (m : ℤ) :
    (if Even m then 1 else s ^ 2) ≠ 0 := by
  by_cases hm : Even m
  · simp [hm]
  · simp [hm, pow_ne_zero 2 hs]
```

---

## Exact repairs inside the strong-induction proof

### 1. Fix the `M % 3 = 0` even-branch placeholder

In the even branch `N = M + M`, after `hM0 : M % 3 = 0`, replace the ambiguous
code

```lean
exact (three_dvd_two_mul_iff.mp ?_)
```

by the direct modular proof.  There are two possible local goal shapes depending
on where the cursor is; use the matching line below.

If the goal is `3 ∣ M`:

```lean
exact Nat.dvd_of_mod_eq_zero hM0
```

If the goal is `3 ∣ M + M`:

```lean
exact (q43_three_dvd_add_self_iff M).2 (Nat.dvd_of_mod_eq_zero hM0)
```

If the goal has already been normalized to `3 ∣ 2 * M`:

```lean
exact (q43_three_dvd_two_mul_iff M).2 (Nat.dvd_of_mod_eq_zero hM0)
```

Do **not** try to prove divisibility from the polynomial equality `hA`; in this
case the divisibility is purely arithmetic from `hM0`.

### 2. Fix all `↑(M+M)` vs `2*↑M` mismatches

Whenever a hypothesis has type

```lean
h : pe W x ((M + M : ℕ) : ℤ) = 0
```

but the current branch/helper expects

```lean
pe W x (2 * (M : ℤ)) = 0
```

insert:

```lean
have h₂ : pe W x (2 * (M : ℤ)) = 0 := by
  simpa [q43_natCast_add_self M] using h
```

Then pass `h₂`, not `h`:

```lean
exact hAne h₂
```

or:

```lean
exact not_three_dvd_two_mul_of_three_dvd_sub_one hm1 hdvd
```

with `hdvd` normalized first if necessary:

```lean
have hdvd₂ : 3 ∣ 2 * M := by
  simpa [two_mul] using hdvd
exact not_three_dvd_two_mul_of_three_dvd_sub_one hm1 hdvd₂
```

If your local divisibility hypothesis is instead `hdvd : 3 ∣ M + M`, use:

```lean
have hdvd₂ : 3 ∣ 2 * M := by
  simpa [two_mul] using hdvd
```

For the odd branch, use the analogous normalization:

```lean
have h₂₁ : pe W x (2 * (M : ℤ) + 1) = 0 := by
  simpa [q43_natCast_add_self_add_one M] using h
```

### 3. Close the odd `M % 3 = 0` nonzero-factor goal

This is the branch where `2*M+1` is not divisible by `3`, `M` itself is
divisible by `3`, and the odd recurrence reduces to `0 - B`.

Paste this pattern at the line with

```lean
have hAne : pe W x (2*(M:ℤ)+1) ≠ 0 := by
  rw [hodd]
```

in the `M % 3 = 0` branch.  The local names assumed below are the standard ones
from your existing proof:

* `ih` is the strong-induction hypothesis;
* the current natural target is `M + M + 1`, so IH calls require bounds such as
  `M - 1 < M + M + 1`;
* `hodd` is the evaluated odd recurrence;
* `hM0 : M % 3 = 0`;
* `hs2 : sx W x ≠ 0`.

```lean
have hM_ge_two : 2 ≤ M := by omega
have hM_ge_one : 1 ≤ M := by omega

have hM_zero : pe W x (M : ℤ) = 0 := by
  have hdiv : 3 ∣ M := Nat.dvd_of_mod_eq_zero hM0
  exact (ih M (by omega)).2 hdiv

have hMm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
  intro hz
  have hzNat : pe W x ((M - 1 : ℕ) : ℤ) = 0 := by
    simpa [q43_natCast_sub_one hM_ge_one] using hz
  have hdiv := (ih (M - 1) (by omega)).1 hzNat
  omega

have hMp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
  intro hz
  have hzNat : pe W x ((M + 1 : ℕ) : ℤ) = 0 := by
    simpa [q43_natCast_add_one M] using hz
  have hdiv := (ih (M + 1) (by omega)).1 hzNat
  omega

have hif_ne : (if Even (M : ℤ) then (1 : k) else sx W x ^ 2) ≠ 0 :=
  q43_ite_even_one_or_sx_sq_ne_zero hs2 (M : ℤ)

have hB_ne :
    pe W x ((M : ℤ) - 1) * pe W x ((M : ℤ) + 1) ^ 3 *
        (if Even (M : ℤ) then (1 : k) else sx W x ^ 2) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hMm1_ne (pow_ne_zero 3 hMp1_ne)) hif_ne

intro hz
apply hB_ne
have hneg :
    -(pe W x ((M : ℤ) - 1) * pe W x ((M : ℤ) + 1) ^ 3 *
        (if Even (M : ℤ) then (1 : k) else sx W x ^ 2)) = 0 := by
  have h := hodd
  rw [hz] at h
  simpa [hM_zero] using h.symm
exact neg_eq_zero.mp hneg
```

If Lean's simplifier leaves association differences in the final `simpa`, replace
the final two lines by:

```lean
have htmp := hodd
rw [hz] at htmp
have htmp' :
    0 = - (pe W x ((M : ℤ) - 1) * pe W x ((M : ℤ) + 1) ^ 3 *
        (if Even (M : ℤ) then (1 : k) else sx W x ^ 2)) := by
  simpa [hM_zero, mul_assoc] using htmp
exact neg_eq_zero.mp htmp'.symm
```

### 4. Close the odd `M % 3 = 2` nonzero-factor goal

This is the branch where `2*M+1` is not divisible by `3`, `M+1` is divisible by
`3`, and the odd recurrence reduces to `A - 0`.

Paste this at the corresponding `hAne` in the `M % 3 = 2` branch.

```lean
have hM_ge_two : 2 ≤ M := by omega

have hMp1_zero : pe W x ((M : ℤ) + 1) = 0 := by
  have hdiv : 3 ∣ M + 1 := by omega
  have hNat := (ih (M + 1) (by omega)).2 hdiv
  simpa [q43_natCast_add_one M] using hNat

have hM_ne : pe W x (M : ℤ) ≠ 0 := by
  intro hz
  have hdiv := (ih M (by omega)).1 hz
  omega

have hMp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
  intro hz
  have hzNat : pe W x ((M + 2 : ℕ) : ℤ) = 0 := by
    simpa [q43_natCast_add_two M] using hz
  have hdiv := (ih (M + 2) (by omega)).1 hzNat
  omega

have hif_ne : (if Even (M : ℤ) then sx W x ^ 2 else (1 : k)) ≠ 0 :=
  q43_ite_even_sx_sq_ne_zero hs2 (M : ℤ)

have hA_fac_ne :
    pe W x ((M : ℤ) + 2) * pe W x (M : ℤ) ^ 3 *
        (if Even (M : ℤ) then sx W x ^ 2 else (1 : k)) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hMp2_ne (pow_ne_zero 3 hM_ne)) hif_ne

intro hz
apply hA_fac_ne
have htmp := hodd
rw [hz] at htmp
simpa [hMp1_zero, mul_assoc] using htmp.symm
```

If the last line leaves the target as `A - 0 = 0`, use:

```lean
have hA_zero :
    pe W x ((M : ℤ) + 2) * pe W x (M : ℤ) ^ 3 *
        (if Even (M : ℤ) then sx W x ^ 2 else (1 : k)) = 0 := by
  have htmp := hodd
  rw [hz] at htmp
  simpa [hMp1_zero, mul_assoc] using htmp.symm
exact hA_zero
```

---

## Replacement statement shape for the full lemma

The theorem header should remain your existing one.  The important signature
shape is:

```lean
theorem preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) (x : k)
    (hs2 : sx W x ≠ 0)
    (hd4 : (W.preΨ 4).eval x ≠ 0)
    (hc3 : (W.Ψ₃).eval x = 0)
    (h4 : (W.preΨ 4).eval x ≠ 0) :
    ∀ N : ℕ, pe W x (N : ℤ) = 0 ↔ 3 ∣ N := by
```

Inside the proof, immediately normalize the two base assumptions:

```lean
  classical
  have h3 : pe W x 3 = 0 := by
    simpa [pe] using hc3
  have h4pe : pe W x 4 ≠ 0 := by
    simpa [pe] using h4
  have hd4pe : pe W x 4 ≠ 0 := by
    simpa [pe] using hd4
```

Use `h4pe` or `hd4pe` consistently in the base case.  Do not use both unless
you need to keep an old local name alive.

For the induction step, normalize every recursive branch before invoking a
hypothesis whose statement is in the `2 * (M : ℤ)` / `2 * (M : ℤ) + 1` form:

```lean
  -- even branch, if the strong induction goal is `M + M`
  have hcast_even : ((M + M : ℕ) : ℤ) = 2 * (M : ℤ) :=
    q43_natCast_add_self M

  -- odd branch, if the strong induction goal is `M + M + 1`
  have hcast_odd : ((M + M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 :=
    q43_natCast_add_self_add_one M
```

Then convert hypotheses explicitly:

```lean
  have h_even_int : pe W x (2 * (M : ℤ)) = 0 := by
    simpa [hcast_even] using h_even_nat

  have h_odd_int : pe W x (2 * (M : ℤ) + 1) = 0 := by
    simpa [hcast_odd] using h_odd_nat
```

This removes the four application type mismatches (`↑(M+M)` vs `2*↑M`).

---

## Why these fixes close the eight errors

1. The `M % 3 = 0` even branch no longer uses an unsynthesized placeholder.
   Divisibility is proved directly from `hM0` by `Nat.dvd_of_mod_eq_zero` and
   the `q43_three_dvd_*` helper in the exact target shape.

2. Every hypothesis of type `pe W x ↑(M+M) = 0` is converted once to
   `pe W x (2*↑M) = 0`, and every hypothesis of type `pe W x ↑(M+M+1) = 0` is
   converted once to `pe W x (2*↑M+1) = 0`.  The converted hypothesis is what
   gets passed to `hAne`, `not_three_dvd_two_mul_of_three_dvd_sub_one`, and the
   analogous branch lemmas.

3. The odd `M % 3 = 0` branch proves the surviving factor
   `pe(M-1) * pe(M+1)^3 * if Even M then 1 else sx^2` is nonzero, then uses
   `pe(M)=0` to reduce the recurrence to `0 - B`; `neg_eq_zero.mp` turns the
   contradiction into `B=0`.

4. The odd `M % 3 = 2` branch proves the surviving factor
   `pe(M+2) * pe(M)^3 * if Even M then sx^2 else 1` is nonzero, then uses
   `pe(M+1)=0` to reduce the recurrence to `A - 0`; the contradiction is
   immediate.

These are the only conceptual changes needed; the rest of your eval-ite fixes
and the `< M + M` IH-bound changes are compatible with this patch.
