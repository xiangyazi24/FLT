# Q1538 (dm1/dm2): replacing `hBodd` by an odd/even parity split

The least-code architecture is **option 1**, but with one important correction:

After dividing the even case by `4`, the normalized identity is not the same as the odd case.

Odd case, with `U = a^4`, `V = 5*b^4`, `B = a*b`:

```lean
4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

Even case, after `M = U/4`, `N = V/4`, `B = 2*B₁`, `B₁ = a*b`:

```lean
r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

So the even branch is not literally the odd branch with `U,V` replaced by `M,N`. You can reuse the **factor splitting** and most of the descent infrastructure, but the Pythagorean kernel must be the normalized even version:

```lean
r ^ 2 = h ^ 2 + (2 * b ^ 2) ^ 2
```

with

```lean
h = a ^ 2 - b ^ 2
```

not the odd-case half

```lean
h = (a ^ 2 - b ^ 2) / 2
```

So do not use option 3. There is no odd-case solution with smaller `B₁`; `(r,B₁,s)` does not satisfy the same quartic equation. Option 2 works but is too much copy-paste. The right split is:

1. Keep your old odd proof as `odd_B_core`.
2. Extract the shared factor-pair descent into helper lemmas.
3. Add a sibling helper for the even-normalized identity.
4. Replace the old `have hBodd : B % 2 = 1 := by sorry` by a `by_cases` parity split.

## Parity wrapper

Use this shape around your old proof body:

```lean
import Mathlib

-- Old proof body should be moved unchanged into this local helper/theorem.
-- It is the code that previously followed
--   have hBodd : B % 2 = 1 := by sorry
-- and used `hBodd`.
have odd_B_core (hBodd : B % 2 = 1) :
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < B.natAbs := by
  -- paste the already-proved odd-B case here, unchanged
  -- except remove the old local `have hBodd := ...`
  exact odd_B_descent_already_proved
    hr hB hcop heq hBodd hr_odd hnonbase

by_cases hBodd : B % 2 = 1
· exact odd_B_core hBodd
· have hBeven : B % 2 = 0 := by
    have hnonneg : 0 ≤ B % 2 :=
      Int.emod_nonneg B (by norm_num : (2 : ℤ) ≠ 0)
    have hlt : B % 2 < 2 :=
      Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 2)
    omega
  -- continue with the even-B branch below
  exact even_B_core hBeven
```

The `hBeven` block is the robust way to convert `¬ B % 2 = 1` into `B % 2 = 0` for integer parity.

## Lean-friendly even branch: avoid `/4` where possible

Even though mathematically you can define `B₁ = B/2`, `M = U/4`, `N = V/4`, in Lean the cleaner path is to obtain witnesses from divisibility:

```lean
import Mathlib

-- U,V are the original factors.
let U : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
let V : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

-- Your helper should give at least these facts.
obtain ⟨hr_odd, hfour_dvd_B, hfour_dvd_U, hfour_dvd_V⟩ :=
  even_B_props hr hB hcop heq hBeven

-- Prefer witnesses over defining by division.
obtain ⟨B₁, hB_eq_two⟩ : ∃ B₁ : ℤ, B = 2 * B₁ := by
  rcases hfour_dvd_B with ⟨C, hBC⟩
  refine ⟨2 * C, ?_⟩
  nlinarith [hBC]

obtain ⟨M, hU_eq_fourM⟩ : ∃ M : ℤ, U = 4 * M := hfour_dvd_U
obtain ⟨N, hV_eq_fourN⟩ : ∃ N : ℤ, V = 4 * N := hfour_dvd_V

have hB₁_pos : 0 < B₁ := by
  nlinarith [hB, hB_eq_two]

have hB₁_natAbs_lt_B : B₁.natAbs < B.natAbs := by
  have hB₁_lt_B : B₁ < B := by
    nlinarith [hB₁_pos, hB_eq_two]
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hB₁_pos) hB₁_lt_B
```

This avoids fighting `Int.ediv` and `%` simplification. If you really want `B₁ = B/2`, add it later:

```lean
have hB₁_eq_div : B₁ = B / 2 := by
  have hmod : B % 2 = 0 := hBeven
  have hdiv := Int.emod_add_ediv B 2
  nlinarith
```

## Normalized `M,N` facts

Assuming you already have the original product identity

```lean
hUV : U * V = 5 * B ^ 4
```

then the halved product is:

```lean
have hMN : M * N = 5 * B₁ ^ 4 := by
  have hraw : (4 * M) * (4 * N) = 5 * (2 * B₁) ^ 4 := by
    simpa [U, V, hU_eq_fourM, hV_eq_fourN, hB_eq_two] using hUV
  nlinarith [hraw]
```

The sum and difference identities are cheap algebra:

```lean
have hMN_sum : M + N = r ^ 2 + 2 * B₁ ^ 2 := by
  have hsum_raw : U + V = 4 * r ^ 2 + 2 * B ^ 2 := by
    dsimp [U, V]
    ring
  have hsum_raw' : 4 * M + 4 * N = 4 * r ^ 2 + 2 * (2 * B₁) ^ 2 := by
    simpa [hU_eq_fourM, hV_eq_fourN, hB_eq_two] using hsum_raw
  nlinarith [hsum_raw']

have hMN_diff : N - M = s := by
  have hdiff_raw : V - U = 4 * s := by
    dsimp [U, V]
    ring
  have hdiff_raw' : 4 * N - 4 * M = 4 * s := by
    simpa [hU_eq_fourM, hV_eq_fourN] using hdiff_raw
  nlinarith [hdiff_raw']
```

For coprimality, do **not** try to reuse `UV_coprime`, because `U,V` are both divisible by `4`. You need the same prime-divisor proof after dividing:

```lean
have hMN_cop : Int.gcd M N = 1 := by
  -- This should be the old `UV_coprime` proof, but run on `M,N`.
  -- Any common prime divisor of `M,N` divides `M+N = r^2 + 2*B₁^2`
  -- and `N-M = s`; combining with the quartic equation and `gcd r B = 1`
  -- gives a contradiction.
  exact MN_coprime_even
    hr hB hcop heq hB_eq_two hU_eq_fourM hV_eq_fourN hMN_sum hMN_diff
```

## Apply the same fourth-power splitter

Now use your existing `coprime_factor_5_fourth` on `M*N = 5*B₁^4`:

```lean
obtain ⟨a, b, ha, hb, hab_cop, hB₁_eq, hfactor⟩ :=
  coprime_factor_5_fourth hB₁_pos hMN_cop hMN

rcases hfactor with ⟨hM_eq, hN_eq⟩ | ⟨hM_eq, hN_eq⟩
```

The two factor cases are:

```lean
-- main even factor case
hM_eq : M = a ^ 4
hN_eq : N = 5 * b ^ 4
hB₁_eq : B₁ = a * b
```

and

```lean
-- symmetric even factor case
hM_eq : M = 5 * a ^ 4
hN_eq : N = b ^ 4
hB₁_eq : B₁ = a * b
```

## Even factor case: main orientation

For `M = a^4`, `N = 5*b^4`, derive the normalized identity and call the even descent core:

```lean
have hid : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
  calc
    r ^ 2 = a ^ 4 + 5 * b ^ 4 - 2 * B₁ ^ 2 := by
      nlinarith [hMN_sum, hM_eq, hN_eq]
    _ = a ^ 4 + 5 * b ^ 4 - 2 * (a * b) ^ 2 := by
      rw [hB₁_eq]
    _ = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
      ring

-- New solution comes from the primitive Pythagorean triple
--   (a^2-b^2)^2 + (2*b^2)^2 = r^2.
-- It returns some B' with B'.natAbs < B₁.natAbs, then we compose with B₁ < B.
obtain ⟨r', B', s', hquartic, hnonbase', hsmall_to_B₁⟩ :=
  descent_even_from_identity_main
    (r := r) (Bbig := B) (C := B₁) (a := a) (b := b)
    hr hB hB₁_pos hB_eq_two hB₁_eq ha hb hab_cop hcop hr_odd hnonbase hid

exact ⟨r', B', s', hquartic, hnonbase', lt_trans hsmall_to_B₁ hB₁_natAbs_lt_B⟩
```

The helper should have this shape:

```lean
lemma descent_even_from_identity_main
    {r Bbig C a b : ℤ}
    (hr : 0 < r) (hBbig : 0 < Bbig) (hCpos : 0 < C)
    (hBbig_eq : Bbig = 2 * C)
    (hCeq : C = a * b)
    (ha : 0 < a) (hb : 0 < b)
    (hab_cop : Int.gcd a b = 1)
    (hcop : Int.gcd r Bbig = 1)
    (hr_odd : r % 2 = 1)
    (hnonbase : ¬ BaseZ r Bbig)
    (hid : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4) :
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < C.natAbs := by
  -- Core proof:
  --   let h := a^2 - b^2
  --   h^2 + (2*b^2)^2 = r^2
  --   primitive Pythagorean parametrization
  --   b^2 = m*n
  --   gcd m n = 1, m,n positive => m = α^2, n = β^2
  --   b = α*β
  --   a^2 = α^4 + α^2*β^2 - β^4
  --   return ⟨α, β, a, ...⟩
  sorry
```

Notice that this helper factors `b^2`, not `b^4`. That is the real difference from the odd-B branch.

## Even factor case: symmetric orientation

For `M = 5*a^4`, `N = b^4`, the normalized identity is:

```lean
have hsym_id : r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
  calc
    r ^ 2 = 5 * a ^ 4 + b ^ 4 - 2 * B₁ ^ 2 := by
      nlinarith [hMN_sum, hM_eq, hN_eq]
    _ = 5 * a ^ 4 + b ^ 4 - 2 * (a * b) ^ 2 := by
      rw [hB₁_eq]
    _ = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
      ring

have hB₁_ba : B₁ = b * a := by
  simpa [mul_comm] using hB₁_eq

have hba_cop : Int.gcd b a = 1 := by
  simpa [Int.gcd_comm] using hab_cop

obtain ⟨r', B', s', hquartic, hnonbase', hsmall_to_B₁⟩ :=
  descent_even_from_identity_main
    (r := r) (Bbig := B) (C := B₁) (a := b) (b := a)
    hr hB hB₁_pos hB_eq_two hB₁_ba hb ha hba_cop hcop hr_odd hnonbase hsym_id

exact ⟨r', B', s', hquartic, hnonbase', lt_trans hsmall_to_B₁ hB₁_natAbs_lt_B⟩
```

This is the even analogue of the `a ↔ b` swap from the odd branch.

## Full skeleton for the replacement

This is the structure I would put around the old proof:

```lean
import Mathlib

have odd_B_core (hBodd : B % 2 = 1) :
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < B.natAbs := by
  -- paste old odd-B proof here
  exact odd_B_descent_already_proved
    hr hB hcop heq hBodd hr_odd hnonbase

by_cases hBodd : B % 2 = 1
· exact odd_B_core hBodd
· have hBeven : B % 2 = 0 := by
    have hnonneg : 0 ≤ B % 2 :=
      Int.emod_nonneg B (by norm_num : (2 : ℤ) ≠ 0)
    have hlt : B % 2 < 2 :=
      Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 2)
    omega

  let U : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
  let V : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

  obtain ⟨hr_odd_even, hfour_dvd_B, hfour_dvd_U, hfour_dvd_V⟩ :=
    even_B_props hr hB hcop heq hBeven

  obtain ⟨B₁, hB_eq_two⟩ : ∃ B₁ : ℤ, B = 2 * B₁ := by
    rcases hfour_dvd_B with ⟨C, hBC⟩
    refine ⟨2 * C, ?_⟩
    nlinarith [hBC]

  obtain ⟨M, hU_eq_fourM⟩ : ∃ M : ℤ, U = 4 * M := hfour_dvd_U
  obtain ⟨N, hV_eq_fourN⟩ : ∃ N : ℤ, V = 4 * N := hfour_dvd_V

  have hB₁_pos : 0 < B₁ := by
    nlinarith [hB, hB_eq_two]

  have hB₁_natAbs_lt_B : B₁.natAbs < B.natAbs := by
    have hB₁_lt_B : B₁ < B := by
      nlinarith [hB₁_pos, hB_eq_two]
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hB₁_pos) hB₁_lt_B

  have hMN : M * N = 5 * B₁ ^ 4 := by
    have hraw : (4 * M) * (4 * N) = 5 * (2 * B₁) ^ 4 := by
      simpa [U, V, hU_eq_fourM, hV_eq_fourN, hB_eq_two] using hUV
    nlinarith [hraw]

  have hMN_sum : M + N = r ^ 2 + 2 * B₁ ^ 2 := by
    have hsum_raw : U + V = 4 * r ^ 2 + 2 * B ^ 2 := by
      dsimp [U, V]
      ring
    have hsum_raw' : 4 * M + 4 * N = 4 * r ^ 2 + 2 * (2 * B₁) ^ 2 := by
      simpa [hU_eq_fourM, hV_eq_fourN, hB_eq_two] using hsum_raw
    nlinarith [hsum_raw']

  have hMN_diff : N - M = s := by
    have hdiff_raw : V - U = 4 * s := by
      dsimp [U, V]
      ring
    have hdiff_raw' : 4 * N - 4 * M = 4 * s := by
      simpa [hU_eq_fourM, hV_eq_fourN] using hdiff_raw
    nlinarith [hdiff_raw']

  have hMN_cop : Int.gcd M N = 1 := by
    exact MN_coprime_even
      hr hB hcop heq hB_eq_two hU_eq_fourM hV_eq_fourN hMN_sum hMN_diff

  obtain ⟨a, b, ha, hb, hab_cop, hB₁_eq, hfactor⟩ :=
    coprime_factor_5_fourth hB₁_pos hMN_cop hMN

  rcases hfactor with ⟨hM_eq, hN_eq⟩ | ⟨hM_eq, hN_eq⟩
  · have hid : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
      calc
        r ^ 2 = a ^ 4 + 5 * b ^ 4 - 2 * B₁ ^ 2 := by
          nlinarith [hMN_sum, hM_eq, hN_eq]
        _ = a ^ 4 + 5 * b ^ 4 - 2 * (a * b) ^ 2 := by
          rw [hB₁_eq]
        _ = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
          ring

    obtain ⟨r', B', s', hquartic, hnonbase', hsmall_to_B₁⟩ :=
      descent_even_from_identity_main
        (r := r) (Bbig := B) (C := B₁) (a := a) (b := b)
        hr hB hB₁_pos hB_eq_two hB₁_eq ha hb hab_cop hcop hr_odd_even hnonbase hid

    exact ⟨r', B', s', hquartic, hnonbase', lt_trans hsmall_to_B₁ hB₁_natAbs_lt_B⟩

  · have hsym_id : r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
      calc
        r ^ 2 = 5 * a ^ 4 + b ^ 4 - 2 * B₁ ^ 2 := by
          nlinarith [hMN_sum, hM_eq, hN_eq]
        _ = 5 * a ^ 4 + b ^ 4 - 2 * (a * b) ^ 2 := by
          rw [hB₁_eq]
        _ = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
          ring

    have hB₁_ba : B₁ = b * a := by
      simpa [mul_comm] using hB₁_eq

    have hba_cop : Int.gcd b a = 1 := by
      simpa [Int.gcd_comm] using hab_cop

    obtain ⟨r', B', s', hquartic, hnonbase', hsmall_to_B₁⟩ :=
      descent_even_from_identity_main
        (r := r) (Bbig := B) (C := B₁) (a := b) (b := a)
        hr hB hB₁_pos hB_eq_two hB₁_ba hb ha hba_cop hcop hr_odd_even hnonbase hsym_id

    exact ⟨r', B', s', hquartic, hnonbase', lt_trans hsmall_to_B₁ hB₁_natAbs_lt_B⟩
```

## Bottom line

Use **option 1**, but the extraction boundary should be:

```lean
coprime factor pair  →  fourth-power split  →  normalized identity  →  descent core
```

not “odd case theorem with `hBodd` removed.”

The even branch builds a smaller solution through `B₁`, then finishes by transitivity:

```lean
B'.natAbs < B₁.natAbs < B.natAbs
```

That is the cleanest Lean architecture and avoids duplicating the full odd-case proof.
