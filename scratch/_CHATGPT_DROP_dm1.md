# Q1738 (dm1): complete even-`B` descent chain for the last sorry

## Main correction

In the even branch the normalized pair is `M,N`, not the raw odd pair.  Therefore the sum identity is

```lean
M + N = r ^ 2 + 2 * B₁ ^ 2
```

with `r = 2*j+1`.  After the oriented split

```lean
M + N = A ^ 4 + 5 * b ^ 4,
B₁ = A * b,
```

the algebra gives

```lean
r ^ 2 = (A ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

not the odd-branch `4*r^2` identity.  This is why the even case needs the extra half-step

```lean
h := A ^ 2 - b ^ 2
u := (r - h) / 2
v := (r + h) / 2
u * v = b ^ 4
```

before applying `pos_fourth_of_coprime_mul_fourth`.

The clean way to write line 564 is to factor out a local oriented payload.  Both branches of `coprime_factor_5_fourth` call the same payload; the second branch just swaps the two factor variables.

## Expected helper shapes

The code below uses the helpers in the following conceptual form.  If your local tuple order differs, only change the `rcases` patterns and the argument order of the helper calls.

```lean
-- coprime_factor_5_fourth hMN_prod hMN_cop hMpos hNpos hB₁_pos
-- returns one of the two oriented splits:
--   inl: ∃ a b, 0 < a ∧ 0 < b ∧ B₁ = a*b ∧ M = a^4 ∧ N = 5*b^4
--   inr: ∃ a b, 0 < a ∧ 0 < b ∧ B₁ = a*b ∧ M = 5*a^4 ∧ N = b^4

-- coprime_rh is the even-half wrapper.  It should consume:
--   0 < r, r % 2 = 1, 0 < b, Int.gcd r b = 1,
--   r^2 = h^2 + 4*b^4
-- and return positive coprime halves u,v with u*v=b^4 and r=u+v, h=v-u.
-- If your current coprime_rh only proves the gcd of the halves, keep its proof
-- and add a tiny wrapper that also packages the positivity/product identities.
```

## Replacement proof spine

Paste this at the last sorry.  The only ambient fact not listed in your message but mathematically necessary is positivity of `r = 2*j+1`.  In the surrounding proof it should be the original `0 < r` fact before rewriting `r` as `2*j+1`; I call it `hr_pos` below.  If your local name differs, replace that one line.

```lean
by
  classical

  let r : ℤ := 2 * j + 1

  have hr_pos' : 0 < r := by
    -- Replace `hr_pos` by the local name of the original positivity fact for `r`.
    -- If the local context still has `0 < 2*j+1` directly, `omega` closes this.
    simpa [r] using hr_pos

  have hr_odd' : r % 2 = 1 := by
    simpa [r] using hr_odd

  have hk_pos : 0 < k := by
    omega

  have hB₁_ge_two : 2 ≤ B₁ := by
    nlinarith [hB₁_val, hk_pos]

  have hB₁_lt_4k : B₁ < 4 * k := by
    nlinarith [hB₁_val, hk_pos]

  have hcop_r4k : Int.gcd r (4 * k) = 1 := by
    simpa [r, hBk] using hcop

  have hnonbase_r4k : ¬ BaseZ r (4 * k) := by
    simpa [r] using hnonbase

  ---------------------------------------------------------------------------
  -- Divisor-of-the-right-parameter coprimality.  We use it with d | B₁ | 4k.
  ---------------------------------------------------------------------------
  have gcd_of_dvd_right :
      ∀ {d : ℤ}, 0 < d → d ∣ B₁ → Int.gcd r d = 1 := by
    intro d hdpos hddvdB₁

    have hB₁_dvd_4k : B₁ ∣ 4 * k := by
      refine ⟨2, ?_⟩
      rw [hB₁_val]
      ring

    have hddvd4k : d ∣ 4 * k := dvd_trans hddvdB₁ hB₁_dvd_4k

    by_contra hbad

    have hgpos : 0 < Int.gcd r d := by
      exact Int.gcd_pos_of_pos_right r hdpos

    have hg_gt_one : 1 < Int.gcd r d := by
      omega

    obtain ⟨p, hp_prime, hp_dvd_g⟩ :=
      Nat.exists_prime_and_dvd (ne_of_gt hg_gt_one)

    have hpZ_prime : Prime (p : ℤ) := by
      exact_mod_cast hp_prime

    have hp_dvd_g_int : (p : ℤ) ∣ (Int.gcd r d : ℤ) := by
      exact_mod_cast hp_dvd_g

    have hpr : (p : ℤ) ∣ r := by
      exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_left r d)

    have hpd : (p : ℤ) ∣ d := by
      exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_right r d)

    have hp4k : (p : ℤ) ∣ 4 * k := dvd_trans hpd hddvd4k

    have hpg : (p : ℤ) ∣ (Int.gcd r (4 * k) : ℤ) := by
      exact Int.dvd_gcd hpr hp4k

    have hpone : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [hcop_r4k] using hpg

    have hpone_nat : p ∣ (1 : ℕ) := by
      exact_mod_cast hpone

    exact hp_prime.not_dvd_one hpone_nat

  ---------------------------------------------------------------------------
  -- Common oriented payload.
  --
  -- Inputs are the variables after choosing the orientation
  --   M + N = A^4 + 5*d^4,   B₁ = A*d.
  -- The second branch of coprime_factor_5_fourth calls this with A and d swapped.
  ---------------------------------------------------------------------------
  have descend_oriented :
      ∀ {A d : ℤ},
        0 < A → 0 < d →
        B₁ = A * d →
        M + N = A ^ 4 + 5 * d ^ 4 →
        ∃ r' B' s',
          QuarticPlusZ r' B' s' ∧
          ¬ BaseZ r' B' ∧
          B'.natAbs < (4 * k).natAbs := by
    intro A d hApos hdpos hB₁_eq hMN_oriented

    have hd_dvd_B₁ : d ∣ B₁ := by
      refine ⟨A, ?_⟩
      rw [hB₁_eq]
      ring

    have hcop_rd : Int.gcd r d = 1 :=
      gcd_of_dvd_right hdpos hd_dvd_B₁

    -------------------------------------------------------------------------
    -- Even-branch algebra: r^2 = (A^2-d^2)^2 + 4*d^4.
    -------------------------------------------------------------------------
    have hsq : r ^ 2 = (A ^ 2 - d ^ 2) ^ 2 + 4 * d ^ 4 := by
      have hsum1 : A ^ 4 + 5 * d ^ 4 = r ^ 2 + 2 * (A * d) ^ 2 := by
        calc
          A ^ 4 + 5 * d ^ 4 = M + N := by
            nlinarith [hMN_oriented]
          _ = r ^ 2 + 2 * B₁ ^ 2 := by
            simpa [r] using hMN_sum
          _ = r ^ 2 + 2 * (A * d) ^ 2 := by
            rw [hB₁_eq]
      nlinarith [hsum1]

    let h : ℤ := A ^ 2 - d ^ 2

    have hsqh : r ^ 2 = h ^ 2 + 4 * d ^ 4 := by
      simpa [h] using hsq

    -------------------------------------------------------------------------
    -- Half-factorization step.
    --
    -- This is the place where the even proof differs from the odd proof.
    -- `coprime_rh` should package:
    --   u = (r-h)/2, v = (r+h)/2,
    --   0<u, 0<v, gcd(u,v)=1, u*v=d^4, r=u+v, h=v-u.
    -------------------------------------------------------------------------
    obtain ⟨u, v, hu_pos, hv_pos, huv_cop, huv_mul, hr_uv, hh_vu⟩ :=
      coprime_rh
        (r := r) (h := h) (b := d)
        hr_pos' hr_odd' hdpos hcop_rd hsqh

    -------------------------------------------------------------------------
    -- Since u*v=d^4 and gcd(u,v)=1, both positive factors are fourth powers.
    -------------------------------------------------------------------------
    obtain ⟨α, β, hαpos, hβpos, hu_eq, hv_eq, hprod_eq⟩ :=
      pos_fourth_of_coprime_mul_fourth
        hu_pos hv_pos huv_cop huv_mul

    -- Some local versions of the expected conclusions.  If your
    -- `pos_fourth_of_coprime_mul_fourth` already returns `d = α*β`, this is
    -- just `exact hprod_eq`.  If it returns only the fourth-power product,
    -- use `eq_of_pos_fourth_eq` as below.
    have hd_eq : d = α * β := by
      first
      | exact hprod_eq
      | apply eq_of_pos_fourth_eq
        · exact hdpos
        · nlinarith [hαpos, hβpos]
        · calc
            d ^ 4 = u * v := by
              nlinarith [huv_mul]
            _ = α ^ 4 * β ^ 4 := by
              rw [hu_eq, hv_eq]
            _ = (α * β) ^ 4 := by
              ring

    -------------------------------------------------------------------------
    -- New quartic solution:
    --   h = v-u = β^4-α^4
    --   h = A^2-d^2
    --   d = αβ
    -- therefore
    --   A^2 = β^4 + α^2β^2 - α^4.
    -------------------------------------------------------------------------
    have hh_eq : h = β ^ 4 - α ^ 4 := by
      nlinarith [hh_vu, hu_eq, hv_eq]

    have hd_sq : d ^ 2 = α ^ 2 * β ^ 2 := by
      rw [hd_eq]
      ring

    have hA_sq : A ^ 2 = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
      calc
        A ^ 2 = h + d ^ 2 := by
          dsimp [h]
          ring
        _ = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
          rw [hh_eq, hd_sq]
          ring

    have hQ : QuarticPlusZ β α A := by
      -- Adjust only the simp list if `QuarticPlusZ` unfolds to the same
      -- polynomial with a different multiplication order.
      simpa [QuarticPlusZ, mul_comm, mul_left_comm, mul_assoc] using hA_sq

    -------------------------------------------------------------------------
    -- New solution is not the base solution.
    -- If α=β=1, then the half data forces A=d=1, hence B₁=A*d=1,
    -- contradicting B₁=2*k with k>0.
    -------------------------------------------------------------------------
    have hnonbase_new : ¬ BaseZ β α := by
      intro hbase

      have hβ_one : β = 1 := by
        simpa [BaseZ] using hbase.1

      have hα_one : α = 1 := by
        simpa [BaseZ] using hbase.2

      have hu_one : u = 1 := by
        rw [hu_eq, hα_one]
        norm_num

      have hv_one : v = 1 := by
        rw [hv_eq, hβ_one]
        norm_num

      have h_zero : h = 0 := by
        nlinarith [hh_vu, hu_one, hv_one]

      have hd_one : d = 1 := by
        have hd_sq_one : d ^ 2 = 1 := by
          dsimp [h] at h_zero
          nlinarith [h_zero]
        nlinarith [hdpos, hd_sq_one]

      have hA_one : A = 1 := by
        dsimp [h] at h_zero
        nlinarith [hApos, h_zero, hd_one]

      have hB₁_one : B₁ = 1 := by
        rw [hB₁_eq, hA_one, hd_one]
        norm_num

      omega

    -------------------------------------------------------------------------
    -- Size drop.  We prove α < B₁ and then B₁ < 4*k.
    -------------------------------------------------------------------------
    have hα_lt_B₁ : α < B₁ := by
      have hB₁_expand : B₁ = A * α * β := by
        rw [hB₁_eq, hd_eq]
        ring

      have hAge1 : 1 ≤ A := by omega
      have hαge1 : 1 ≤ α := by omega
      have hβge1 : 1 ≤ β := by omega

      have hAβ_ne_one : A * β ≠ 1 := by
        intro hAβ

        have hA_one : A = 1 := by
          nlinarith [hAge1, hβge1, hAβ]

        have hβ_one : β = 1 := by
          nlinarith [hAge1, hβge1, hAβ]

        have hh_eq_one : h = 1 - α ^ 4 := by
          nlinarith [hh_eq, hβ_one]

        have hd_eq_alpha : d = α := by
          nlinarith [hd_eq, hβ_one]

        have hh_eq_two : h = 1 - α ^ 2 := by
          dsimp [h]
          nlinarith [hA_one, hd_eq_alpha]

        have hα_one : α = 1 := by
          nlinarith [hαpos, hh_eq_one, hh_eq_two]

        have hd_one : d = 1 := by
          nlinarith [hd_eq_alpha, hα_one]

        have hB₁_one : B₁ = 1 := by
          rw [hB₁_eq, hA_one, hd_one]
          norm_num

        omega

      have hAβ_ge_two : 2 ≤ A * β := by
        have hAβ_ge_one : 1 ≤ A * β := by
          nlinarith [hAge1, hβge1]
        omega

      rw [hB₁_expand]
      nlinarith [hAβ_ge_two, hαge1]

    have hα_lt_4k : α < 4 * k := lt_trans hα_lt_B₁ hB₁_lt_4k

    have hdrop : α.natAbs < (4 * k).natAbs := by
      have hα_nonneg : 0 ≤ α := le_of_lt hαpos
      have h4k_nonneg : 0 ≤ 4 * k := by nlinarith [hk_pos]
      rw [Int.natAbs_of_nonneg hα_nonneg, Int.natAbs_of_nonneg h4k_nonneg]
      exact_mod_cast hα_lt_4k

    exact ⟨β, α, A, hQ, hnonbase_new, hdrop⟩

  ---------------------------------------------------------------------------
  -- Now run the project-local coprime factorization of M*N=5*B₁^4.
  ---------------------------------------------------------------------------
  rcases coprime_factor_5_fourth
      hMN_prod hMN_cop hMpos hNpos hB₁_pos with hsplit | hsplit

  · -------------------------------------------------------------------------
    -- Branch 1: M=a^4, N=5*b^4, B₁=a*b.
    -------------------------------------------------------------------------
    rcases hsplit with ⟨a, b, ha_pos, hb_pos, hB₁_ab, hM_a, hN_b⟩

    apply descend_oriented ha_pos hb_pos hB₁_ab

    calc
      M + N = a ^ 4 + 5 * b ^ 4 := by
        rw [hM_a, hN_b]

  · -------------------------------------------------------------------------
    -- Branch 2: M=5*a^4, N=b^4.  Swap orientation: A=b, d=a.
    -------------------------------------------------------------------------
    rcases hsplit with ⟨a, b, ha_pos, hb_pos, hB₁_ab, hM_a, hN_b⟩

    apply descend_oriented hb_pos ha_pos
    · -- B₁ = b*a
      rw [hB₁_ab]
      ring
    · calc
        M + N = b ^ 4 + 5 * a ^ 4 := by
          rw [hM_a, hN_b]
          ring
```

## If `coprime_rh` only returns the gcd

If your existing helper has the older shape

```lean
coprime_rh : Int.gcd ((r-h)/2) ((r+h)/2) = 1
```

then add this wrapper next to it and keep the main proof above unchanged.  The wrapper is where all `/2` divisibility bookkeeping belongs; do not inline it into the final descent proof.

```lean
/-- Even-branch half factorization package. -/
private theorem coprime_rh_pack
    {r h b : ℤ}
    (hr_pos : 0 < r) (hr_odd : r % 2 = 1)
    (hb_pos : 0 < b)
    (hcop_rb : Int.gcd r b = 1)
    (hsq : r ^ 2 = h ^ 2 + 4 * b ^ 4) :
    ∃ u v : ℤ,
      0 < u ∧ 0 < v ∧
      Int.gcd u v = 1 ∧
      u * v = b ^ 4 ∧
      r = u + v ∧
      h = v - u := by
  -- This is the canonical proof:
  -- 1. `h` is odd from `hsq` mod 2 and `hr_odd`.
  -- 2. Hence `2 ∣ r-h` and `2 ∣ r+h`; choose witnesses `u,v`.
  -- 3. Positivity follows from `r^2 = h^2 + 4*b^4`, `hb_pos`, and `hr_pos`,
  --    giving `-|r| < h < |r|`, hence `0 < r-h` and `0 < r+h`.
  -- 4. `(r-h)(r+h)=4*b^4`; substituting the witnesses gives `u*v=b^4`.
  -- 5. The gcd is your existing `coprime_rh` proof.
  --
  -- I would keep this as a separate helper because it is exactly the fragile
  -- parity/division layer, whereas the descent proof above is pure algebra.
  sorry
```

The main descent code should call the package-returning helper.  If you keep the wrapper name `coprime_rh_pack`, replace the one call in the main proof by:

```lean
obtain ⟨u, v, hu_pos, hv_pos, huv_cop, huv_mul, hr_uv, hh_vu⟩ :=
  coprime_rh_pack
    (r := r) (h := h) (b := d)
    hr_pos' hr_odd' hdpos hcop_rd hsqh
```

## Why this closes the requested goal

The returned witness is

```lean
r' = β,
B' = α,
s' = A.
```

The new quartic equation is exactly

```lean
A ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4
```

up to multiplication order.  The size drop is

```lean
α < B₁ = A*d = A*α*β < 4*k
```

where strictness in the first inequality is forced by the nontrivial/even normalized branch: equality would force `A=β=α=d=1`, hence `B₁=1`, contradicting `B₁=2*k` and `k>0`.