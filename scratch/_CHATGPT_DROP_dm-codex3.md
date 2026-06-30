# Q2492 weak primitive four-square AP residuals Lean audit

Source note: the GitHub connector could not fetch `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean` from branch `main` (`404 Not Found`), and repository code search did not find `WeakPrimitiveAPParity`. So this audit is grounded in the definitions pasted in the prompt, not in local-only file contents under `/Users/huangx/repos/flt-ai`.

## Truth audit

Both stated residuals are mathematically true.

### `WeakPrimitiveAPParity`

True. Modulo `4`, integer squares are only `0` or `1`. A length-four arithmetic progression whose entries all lie in `{0,1}` must be constant modulo `4`. Therefore the four roots are all even or all odd. The hypothesis

```lean
rootGCD4 p q r s = 1
```

excludes the all-even case, because then `2` divides all four `natAbs` values and hence divides the nested gcd. Thus all roots are odd. Odd squares are congruent to `1` modulo `8`, so

```lean
Δ = q^2 - p^2
```

is divisible by `8`.

### `WeakPrimitiveAPPairwise`

True, with the displayed oddness assumptions. If an odd prime `ℓ` divides two adjacent roots, then `ℓ ∣ Δ`, and the AP equations propagate `ℓ` to the other two roots. If `ℓ` divides roots at distance two, then `ℓ ∣ 2*Δ`; oddness gives `ℓ ≠ 2`, so `ℓ ∣ Δ`, and propagation again gives all four roots. If `ℓ` divides the endpoints `p` and `s`, then `3*Δ = s^2 - p^2`; for `ℓ ≠ 3`, cancel `3`. For `ℓ = 3`, use the square-residue table mod `3`: with `p^2 = s^2 = 0`, the middle residues would be `Δ` and `2*Δ`, and both can be squares mod `3` only if `Δ = 0`, so `q,r` are also divisible by `3`. In all cases a prime common divisor of any pair divides all four roots, contradicting `rootGCD4 = 1`.

## Drop-in parity route

Put these after the definitions of `rootGCD4` and `WeakPrimitiveAPParity`. The code uses a small finite `ZMod 4` case split plus one odd-square mod-8 lemma.

```lean
import Mathlib

/-- A four-term AP of squares modulo `4` has either all even roots mod `4`
    or all odd roots mod `4`. -/
lemma zmod4_four_square_ap_roots_even_or_odd
    (P Q R S Δ : ZMod 4)
    (hpq : Q ^ 2 - P ^ 2 = Δ)
    (hqr : R ^ 2 - Q ^ 2 = Δ)
    (hrs : S ^ 2 - R ^ 2 = Δ) :
    ((P = 0 ∨ P = 2) ∧ (Q = 0 ∨ Q = 2) ∧
      (R = 0 ∨ R = 2) ∧ (S = 0 ∨ S = 2)) ∨
    ((P = 1 ∨ P = 3) ∧ (Q = 1 ∨ Q = 3) ∧
      (R = 1 ∨ R = 3) ∧ (S = 1 ∨ S = 3)) := by
  fin_cases P <;> fin_cases Q <;> fin_cases R <;>
    fin_cases S <;> fin_cases Δ <;>
    norm_num at hpq hqr hrs ⊢

lemma int_mod2_eq_one_of_zmod4_eq_one_or_three {x : ℤ}
    (h : (x : ZMod 4) = 1 ∨ (x : ZMod 4) = 3) :
    x % 2 = 1 := by
  rcases h with h1 | h3
  · have h1' : (x : ZMod 4) = ((1 : ℤ) : ZMod 4) := by
      simpa using h1
    have hm : x ≡ (1 : ℤ) [ZMOD 4] :=
      (CharP.intCast_eq_intCast (ZMod 4) 4).mp h1'
    change x % (4 : ℤ) = (1 : ℤ) % (4 : ℤ) at hm
    norm_num at hm
    omega
  · have h3' : (x : ZMod 4) = ((3 : ℤ) : ZMod 4) := by
      simpa using h3
    have hm : x ≡ (3 : ℤ) [ZMOD 4] :=
      (CharP.intCast_eq_intCast (ZMod 4) 4).mp h3'
    change x % (4 : ℤ) = (3 : ℤ) % (4 : ℤ) at hm
    norm_num at hm
    omega

lemma two_dvd_natAbs_of_zmod4_eq_zero_or_two {x : ℤ}
    (h : (x : ZMod 4) = 0 ∨ (x : ZMod 4) = 2) :
    2 ∣ x.natAbs := by
  have hx2 : x % (2 : ℤ) = 0 := by
    rcases h with h0 | h2
    · have h0' : (x : ZMod 4) = ((0 : ℤ) : ZMod 4) := by
        simpa using h0
      have hm : x ≡ (0 : ℤ) [ZMOD 4] :=
        (CharP.intCast_eq_intCast (ZMod 4) 4).mp h0'
      change x % (4 : ℤ) = (0 : ℤ) % (4 : ℤ) at hm
      norm_num at hm
      omega
    · have h2' : (x : ZMod 4) = ((2 : ℤ) : ZMod 4) := by
        simpa using h2
      have hm : x ≡ (2 : ℤ) [ZMOD 4] :=
        (CharP.intCast_eq_intCast (ZMod 4) 4).mp h2'
      change x % (4 : ℤ) = (2 : ℤ) % (4 : ℤ) at hm
      norm_num at hm
      omega
  have hxEven : Even x := by
    rw [even_iff_two_dvd]
    rw [Int.dvd_iff_emod_eq_zero]
    exact hx2
  exact even_iff_two_dvd.mp hxEven.natAbs

lemma int_sq_modEq_one_mod8_of_mod2_eq_one {x : ℤ}
    (hx : x % 2 = 1) :
    x ^ 2 ≡ 1 [ZMOD 8] := by
  have hodd : Odd x := by
    rw [Int.odd_iff]
    exact hx
  rcases hodd with ⟨k, rfl⟩
  rw [Int.modEq_iff_dvd]
  have h2 : (2 : ℤ) ∣ k * (k + 1) := Int.two_dvd_mul_add_one k
  rcases h2 with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  calc
    1 - (2 * k + 1) ^ 2 = -(4 * (k * (k + 1))) := by ring
    _ = 8 * (-t) := by
      rw [ht]
      ring

theorem weakPrimitiveAPParity_proof : WeakPrimitiveAPParity := by
  intro p q r s Δ hpq hqr hrs hroot
  have hpq4 : (q : ZMod 4) ^ 2 - (p : ZMod 4) ^ 2 = (Δ : ZMod 4) := by
    have := congrArg (fun z : ℤ => (z : ZMod 4)) hpq
    simpa using this
  have hqr4 : (r : ZMod 4) ^ 2 - (q : ZMod 4) ^ 2 = (Δ : ZMod 4) := by
    have := congrArg (fun z : ℤ => (z : ZMod 4)) hqr
    simpa using this
  have hrs4 : (s : ZMod 4) ^ 2 - (r : ZMod 4) ^ 2 = (Δ : ZMod 4) := by
    have := congrArg (fun z : ℤ => (z : ZMod 4)) hrs
    simpa using this
  rcases zmod4_four_square_ap_roots_even_or_odd
      (p : ZMod 4) (q : ZMod 4) (r : ZMod 4) (s : ZMod 4) (Δ : ZMod 4)
      hpq4 hqr4 hrs4 with hEven | hOdd
  · exfalso
    rcases hEven with ⟨hpE, hqE, hrE, hsE⟩
    have hp2 : 2 ∣ p.natAbs := two_dvd_natAbs_of_zmod4_eq_zero_or_two hpE
    have hq2 : 2 ∣ q.natAbs := two_dvd_natAbs_of_zmod4_eq_zero_or_two hqE
    have hr2 : 2 ∣ r.natAbs := two_dvd_natAbs_of_zmod4_eq_zero_or_two hrE
    have hs2 : 2 ∣ s.natAbs := two_dvd_natAbs_of_zmod4_eq_zero_or_two hsE
    have h2root : 2 ∣ rootGCD4 p q r s := by
      unfold rootGCD4
      exact Nat.dvd_gcd hp2 (Nat.dvd_gcd hq2 (Nat.dvd_gcd hr2 hs2))
    have h21 : 2 ∣ (1 : ℕ) := by
      simpa [hroot] using h2root
    norm_num at h21
  · rcases hOdd with ⟨hpO, hqO, hrO, hsO⟩
    have hp1 : p % 2 = 1 := int_mod2_eq_one_of_zmod4_eq_one_or_three hpO
    have hq1 : q % 2 = 1 := int_mod2_eq_one_of_zmod4_eq_one_or_three hqO
    have hr1 : r % 2 = 1 := int_mod2_eq_one_of_zmod4_eq_one_or_three hrO
    have hs1 : s % 2 = 1 := int_mod2_eq_one_of_zmod4_eq_one_or_three hsO
    have h8Δ : (8 : ℤ) ∣ Δ := by
      have hq8 : q ^ 2 ≡ 1 [ZMOD 8] := int_sq_modEq_one_mod8_of_mod2_eq_one hq1
      have hp8 : p ^ 2 ≡ 1 [ZMOD 8] := int_sq_modEq_one_mod8_of_mod2_eq_one hp1
      have hdiff : q ^ 2 - p ^ 2 ≡ 0 [ZMOD 8] := by
        simpa using hq8.sub hp8
      have hΔmod : Δ ≡ 0 [ZMOD 8] := by
        simpa [hpq] using hdiff
      exact Int.modEq_zero_iff_dvd.mp hΔmod
    exact ⟨hp1, hq1, hr1, hs1, h8Δ⟩
```

If the theorem name expected by the file is a residual theorem with another name, keep the proof body and change only this line:

```lean
theorem weakPrimitiveAPParity_proof : WeakPrimitiveAPParity := by
```

## Pairwise route

For pairwise, I would not start with the six `Int.gcd` goals directly. First add the following small root-gcd helpers; these are independent and should compile immediately.

```lean
lemma rootGCD4_dvd_p (p q r s : ℤ) :
    rootGCD4 p q r s ∣ p.natAbs := by
  unfold rootGCD4
  exact Nat.gcd_dvd_left _ _

lemma rootGCD4_dvd_q (p q r s : ℤ) :
    rootGCD4 p q r s ∣ q.natAbs := by
  unfold rootGCD4
  exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)

lemma rootGCD4_dvd_r (p q r s : ℤ) :
    rootGCD4 p q r s ∣ r.natAbs := by
  unfold rootGCD4
  exact (Nat.gcd_dvd_right _ _).trans
    ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))

lemma rootGCD4_dvd_s (p q r s : ℤ) :
    rootGCD4 p q r s ∣ s.natAbs := by
  unfold rootGCD4
  exact (Nat.gcd_dvd_right _ _).trans
    ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))

lemma false_of_prime_dvd_all_roots_of_rootGCD4_eq_one
    {p q r s : ℤ} {ℓ : ℕ}
    (hroot : rootGCD4 p q r s = 1)
    (hℓ : ℓ.Prime)
    (hp : ℓ ∣ p.natAbs)
    (hq : ℓ ∣ q.natAbs)
    (hr : ℓ ∣ r.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    False := by
  have hℓroot : ℓ ∣ rootGCD4 p q r s := by
    unfold rootGCD4
    exact Nat.dvd_gcd hp (Nat.dvd_gcd hq (Nat.dvd_gcd hr hs))
  have hℓone : ℓ ∣ (1 : ℕ) := by
    simpa [hroot] using hℓroot
  have hle : ℓ ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hℓone
  exact (not_lt_of_ge hle) hℓ.one_lt
```

Then add pair-propagation helpers. I recommend stating them over Nat divisibility of `natAbs`, because the final gcd goals are Nat-valued anyway. These are the exact statements I would add next.

```lean
-- Target helper 1: adjacent pair propagation.
-- For `(p,q)`, `(q,r)`, and `(r,s)`, prove versions with the obvious substitutions.
-- theorem prime_dvd_all_of_dvd_pq
--     {p q r s Δ : ℤ} {ℓ : ℕ}
--     (hℓ : ℓ.Prime)
--     (hℓodd : ℓ ≠ 2)
--     (hpq : q ^ 2 - p ^ 2 = Δ)
--     (hqr : r ^ 2 - q ^ 2 = Δ)
--     (hrs : s ^ 2 - r ^ 2 = Δ)
--     (hp : ℓ ∣ p.natAbs)
--     (hq : ℓ ∣ q.natAbs) :
--     ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs

-- Target helper 2: distance-two propagation.
-- theorem prime_dvd_all_of_dvd_pr
--     {p q r s Δ : ℤ} {ℓ : ℕ}
--     (hℓ : ℓ.Prime)
--     (hℓodd : ℓ ≠ 2)
--     (hpq : q ^ 2 - p ^ 2 = Δ)
--     (hqr : r ^ 2 - q ^ 2 = Δ)
--     (hrs : s ^ 2 - r ^ 2 = Δ)
--     (hp : ℓ ∣ p.natAbs)
--     (hr : ℓ ∣ r.natAbs) :
--     ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs

-- Target helper 3: endpoint propagation, with special `ℓ = 3` branch.
-- theorem prime_dvd_all_of_dvd_ps
--     {p q r s Δ : ℤ} {ℓ : ℕ}
--     (hℓ : ℓ.Prime)
--     (hℓodd : ℓ ≠ 2)
--     (hpq : q ^ 2 - p ^ 2 = Δ)
--     (hqr : r ^ 2 - q ^ 2 = Δ)
--     (hrs : s ^ 2 - r ^ 2 = Δ)
--     (hp : ℓ ∣ p.natAbs)
--     (hs : ℓ ∣ s.natAbs) :
--     ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs
```

The propagation proof pattern is:

1. Convert `ℓ ∣ x.natAbs` to `((ℓ : ℤ) ∣ x)` when doing equation arithmetic. The API to grep is likely one of:

```lean
#check Int.natAbs_dvd
#check Int.dvd_natAbs
#check Int.natCast_dvd_natCast
#check Int.natAbs_mul
#check Int.natAbs_pow
```

If the exact bridge is annoying, add a local bridge once:

```lean
-- theorem natPrime_dvd_natAbs_iff_int_dvd {ℓ : ℕ} {x : ℤ} :
--     ℓ ∣ x.natAbs ↔ ((ℓ : ℤ) ∣ x)
```

2. From `ℓ ∣ x`, get `ℓ ∣ x^2` by `pow_dvd_pow_of_dvd` or `dvd_mul_of_dvd_left/right`.

3. Adjacent case: if `ℓ ∣ p` and `ℓ ∣ q`, then `ℓ ∣ q^2 - p^2 = Δ`; then `ℓ ∣ r^2 = q^2 + Δ`, hence `ℓ ∣ r` by `Nat.Prime.dvd_of_dvd_pow` after crossing back to `natAbs`; similarly for `s`.

4. Distance-two case: from `ℓ ∣ p,r`, get `ℓ ∣ r^2 - p^2 = 2*Δ`; since `ℓ ≠ 2`, `Nat.Prime.coprime_iff_not_dvd` or `Nat.Prime.dvd_mul` gives `ℓ ∣ Δ`; then propagate.

5. Endpoint case: from `ℓ ∣ p,s`, get `ℓ ∣ 3*Δ`. If `ℓ ≠ 3`, cancel as above. If `ℓ = 3`, use a `ZMod 3` finite residue helper:

```lean
lemma zmod3_endpoint_square_ap_forces_middle_zero
    (P Q R S Δ : ZMod 3)
    (hp : P = 0) (hs : S = 0)
    (hpq : Q ^ 2 - P ^ 2 = Δ)
    (hqr : R ^ 2 - Q ^ 2 = Δ)
    (hrs : S ^ 2 - R ^ 2 = Δ) :
    Q = 0 ∧ R = 0 := by
  fin_cases P <;> fin_cases Q <;> fin_cases R <;>
    fin_cases S <;> fin_cases Δ <;>
    norm_num at hp hs hpq hqr hrs ⊢
```

Finally, each pairwise gcd goal is best proved by the same wrapper:

```lean
-- Target wrapper for one pair; instantiate with each pair and its propagation lemma.
-- theorem int_gcd_eq_one_of_no_prime_common_pair
--     {x y p q r s : ℤ}
--     (hroot : rootGCD4 p q r s = 1)
--     (hprop : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ≠ 2 →
--       ℓ ∣ x.natAbs → ℓ ∣ y.natAbs →
--       ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs)
--     (hxodd : x % 2 = 1) :
--     Int.gcd x y = 1
```

Inside this wrapper:

```lean
rw [Int.gcd_def]
rw [Nat.coprime_iff_gcd_eq_one]
refine Nat.coprime_of_dvd' ?_
intro ℓ hℓ hx hy
have hℓne2 : ℓ ≠ 2 := by
  intro h2
  subst h2
  -- `hxodd` contradicts `2 ∣ x.natAbs`; use the same `Even.natAbs` bridge as above.
  ...
rcases hprop hℓ hℓne2 hx hy with ⟨hp, hq, hr, hs⟩
exact False.elim (false_of_prime_dvd_all_roots_of_rootGCD4_eq_one hroot hℓ hp hq hr hs)
```

This keeps the six final goals small and avoids duplicating the AP propagation proof six times.

## APIs to check locally

```lean
#check ZMod
#check fin_cases
#check CharP.intCast_eq_intCast
#check Int.modEq_iff_dvd
#check Int.modEq_zero_iff_dvd
#check Int.ModEq.sub
#check Int.two_dvd_mul_add_one
#check Int.odd_iff
#check Int.natAbs_odd
#check even_iff_two_dvd
#check Nat.dvd_gcd
#check Nat.gcd_dvd_left
#check Nat.gcd_dvd_right
#check Nat.coprime_of_dvd'
#check Nat.Prime.dvd_of_dvd_pow
#check Nat.Prime.dvd_mul
#check Nat.Prime.coprime_iff_not_dvd
#check Nat.le_of_dvd
#check Int.gcd_def
```

## Practical insertion order

1. Add the `ZMod 4` parity helper and the three conversion lemmas.
2. Add `weakPrimitiveAPParity_proof` and verify it independently.
3. Add `rootGCD4_dvd_*` and `false_of_prime_dvd_all_roots_of_rootGCD4_eq_one`.
4. Add propagation helpers one distance class at a time: adjacent, distance two, endpoint.
5. Finish `WeakPrimitiveAPPairwise` by a single pair-wrapper instantiated six times.
