# Q1738 (dm1): even-`B` descent chain for the last sorry

## Main correction

In the even branch the normalized pair is `M,N`, not the raw odd pair.  Therefore the sum identity is

```lean
M + N = r ^ 2 + 2 * B₁ ^ 2
```

with `r = 2*j+1`.  After an oriented split

```lean
M + N = A ^ 4 + 5 * d ^ 4,
B₁ = A * d,
```

the algebra gives

```lean
r ^ 2 = (A ^ 2 - d ^ 2) ^ 2 + 4 * d ^ 4
```

not the odd-branch `4*r^2` identity.  That is exactly why the even proof needs the extra half-step

```lean
h := A ^ 2 - d ^ 2
u := (r - h) / 2
v := (r + h) / 2
u * v = d ^ 4
```

before `pos_fourth_of_coprime_mul_fourth`.

The proof below factors out one local oriented payload.  The second branch of `coprime_factor_5_fourth` calls the same payload with the factor variables swapped.

## Helper interfaces used

The proof uses the helpers in the following conceptual shape.  If your exact local tuple order differs, change only the `rcases` patterns and the helper argument order.

```lean
-- coprime_factor_5_fourth hMN_prod hMN_cop hMpos hNpos hB₁_pos
-- returns either
--   ∃ a b, 0<a ∧ 0<b ∧ B₁=a*b ∧ M=a^4 ∧ N=5*b^4
-- or
--   ∃ a b, 0<a ∧ 0<b ∧ B₁=a*b ∧ M=5*a^4 ∧ N=b^4

-- coprime_rh is used as the even-half package:
--   coprime_rh hr_pos hr_odd hb_pos hcop_rb hsqh
-- returns u,v with
--   0<u, 0<v, gcd(u,v)=1, u*v=b^4, r=u+v, h=v-u.
```

The only ambient fact not listed in the prompt but mathematically necessary is positivity of `r = 2*j+1`.  In the surrounding proof it should be the original `0 < r` before rewriting `r` as `2*j+1`; I call it `hr_pos` below.

## Replacement for the last sorry

```lean
by
  classical

  let r : ℤ := 2 * j + 1

  have hr_pos' : 0 < r := by
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

  ---------------------------------------------------------------------------
  -- If d | B₁, then gcd(r,d)=1 because B₁ | 4k and gcd(r,4k)=1.
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
  -- Common oriented descent payload.
  -- Inputs:
  --   0<A, 0<d, B₁=A*d, M+N=A^4+5*d^4.
  -- Output:
  --   (β, α, A) is a new non-base solution and α < 4k.
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
    -- Even normalized algebra.
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
    -- Half layer: u=(r-h)/2, v=(r+h)/2.
    -------------------------------------------------------------------------
    obtain ⟨u, v, hu_pos, hv_pos, huv_cop, huv_mul, hr_uv, hh_vu⟩ :=
      coprime_rh
        (r := r) (h := h) (b := d)
        hr_pos' hr_odd' hdpos hcop_rd hsqh

    -------------------------------------------------------------------------
    -- u and v are coprime positive fourth powers.
    -------------------------------------------------------------------------
    obtain ⟨α, β, hαpos, hβpos, hu_eq, hv_eq, hd_eq⟩ :=
      pos_fourth_of_coprime_mul_fourth
        hu_pos hv_pos huv_cop huv_mul

    -- If your local `pos_fourth_of_coprime_mul_fourth` returns only
    -- `(α*β)^4 = d^4`, replace `hd_eq` above by:
    --
    --   have hd_eq : d = α*β := by
    --     apply eq_of_pos_fourth_eq
    --     · exact hdpos
    --     · nlinarith [hαpos, hβpos]
    --     · calc
    --         d^4 = u*v := by nlinarith [huv_mul]
    --         _ = α^4 * β^4 := by rw [hu_eq, hv_eq]
    --         _ = (α*β)^4 := by ring

    -------------------------------------------------------------------------
    -- New quartic equation.
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
      simpa [QuarticPlusZ, mul_comm, mul_left_comm, mul_assoc] using hA_sq

    -------------------------------------------------------------------------
    -- Non-base: BaseZ β α would force α=β=1, hence A=d=1 and B₁=1,
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
    -- Size drop: α < B₁ and B₁ < 4k.
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
  -- Factor M*N=5*B₁^4 and feed both orientations into descend_oriented.
  ---------------------------------------------------------------------------
  rcases coprime_factor_5_fourth
      hMN_prod hMN_cop hMpos hNpos hB₁_pos with hsplit | hsplit

  · rcases hsplit with ⟨a, b, ha_pos, hb_pos, hB₁_ab, hM_a, hN_b⟩

    apply descend_oriented ha_pos hb_pos hB₁_ab

    calc
      M + N = a ^ 4 + 5 * b ^ 4 := by
        rw [hM_a, hN_b]

  · rcases hsplit with ⟨a, b, ha_pos, hb_pos, hB₁_ab, hM_a, hN_b⟩

    apply descend_oriented hb_pos ha_pos
    · rw [hB₁_ab]
      ring
    · calc
        M + N = b ^ 4 + 5 * a ^ 4 := by
          rw [hM_a, hN_b]
          ring
```

## Notes for integration

1. The line `simpa [r] using hr_pos` is the only place that depends on the local name for positivity of `2*j+1`.
2. If `BaseZ` is not literally a pair/proposition exposing `.1` and `.2`, replace the two lines extracting `hβ_one` and `hα_one` with the destructor already used in your odd-case proof.
3. If `pos_fourth_of_coprime_mul_fourth` returns a fourth-power equality rather than `d = α*β`, use the `eq_of_pos_fourth_eq` block in the comment.
4. The second factorization branch is not a new proof.  It is the same oriented proof with `(A,d)=(b,a)`.