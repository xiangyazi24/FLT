# Q1530 (dm1): symmetric quartic descent branch

Yes: the second factor case is the same descent with the roles of the two factor variables swapped. But this is **not** a symmetry of the original quartic equation in `r` and `B`; it is only a symmetry of the extracted factor-pair descent argument.

For the branch

```lean
hU_eq : 2 * r ^ 2 + B ^ 2 - 2 * s = 5 * a ^ 4
hV_eq : 2 * r ^ 2 + B ^ 2 + 2 * s = b ^ 4
hB_eq : B = a * b
```

the descent variable is `a`, not `b`. So the clean proof is the main proof with the abstract variables

```lean
x := b   -- the new `s'`
y := a   -- the descent variable / fourth-power factor
```

and with

```lean
h := (b ^ 2 - a ^ 2) / 2
```

not `(a ^ 2 - b ^ 2) / 2`.

The short branch body should look like this, assuming the already-proved main descent has been factored as a lemma/local theorem that takes the identity

```lean
4 * r ^ 2 = (x ^ 2 - y ^ 2) ^ 2 + 4 * y ^ 4
```

and then constructs the smaller solution `(β, α, x)`:

```lean
-- symmetric factor branch: U = 5*a^4, V = b^4

have hB_ba : B = b * a := by
  simpa [mul_comm] using hB_eq

have hba_cop : Int.gcd b a = 1 := by
  simpa [Int.gcd_comm] using hab_cop

-- This is the gcd needed by the copied descent: gcd(r, descent-variable) = 1.
-- Use whatever local lemma you already used in the main case for extracting
-- coprimality from `Int.gcd r B = 1` and a divisor of `B`.
have ha_dvd_B : a ∣ B := by
  refine ⟨b, ?_⟩
  rw [hB_eq]
  ring

have hra_cop : Int.gcd r a = 1 := by
  -- Replace this line by the exact gcd-divisor helper in your file if it has
  -- a different name.  This is the only new gcd input compared with the main
  -- branch, where the corresponding fact was `Int.gcd r b = 1`.
  exact gcd_of_gcd_mul_right_eq_one hcop ha_dvd_B

have hsym_id :
    4 * r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
  have hsum : 4 * r ^ 2 + 2 * B ^ 2 = 5 * a ^ 4 + b ^ 4 := by
    nlinarith [hU_eq, hV_eq]
  calc
    4 * r ^ 2 = 5 * a ^ 4 + b ^ 4 - 2 * B ^ 2 := by
      nlinarith [hsum]
    _ = 5 * a ^ 4 + b ^ 4 - 2 * (a * b) ^ 2 := by
      rw [hB_eq]
    _ = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
      ring

-- This is the desired one-line reuse of the main-case descent kernel.
-- The important swapped arguments are `(x := b)` and `(y := a)`.
exact descent_from_square_identity
  (r := r) (B := B) (x := b) (y := a)
  hb ha hr hB
  hB_ba hba_cop hra_cop
  hBodd hr_odd hnonbase
  hsym_id
```

Here `descent_from_square_identity` is the abstraction of your completed 80-line main-case proof. Its internal conclusion should be exactly the current goal:

```lean
∃ r' B' s' : ℤ,
  QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < B.natAbs
```

If you have **not** extracted that kernel, then there is no Lean magic that turns the first branch proof into the second branch proof. `swap` swaps goals, not variables; `.symm` reverses equalities, not scripts. In that case, literally copy the main branch and make these substitutions:

```text
main variable a          ↦ b
main variable b          ↦ a
main descent h           ↦ (b^2 - a^2) / 2
main gcd(r,b) fact       ↦ gcd(r,a) fact, from a ∣ B
main identity            ↦ 4*r^2 = (b^2-a^2)^2 + 4*a^4
main factor              ↦ (r-h)*(r+h) = a^4
main new solution         ↦ (β, α, b)
main smaller-bound target ↦ α.natAbs < B.natAbs, via α < a ≤ a*b = B
```

The sign convention is the only real trap. With

```lean
let h : ℤ := (b ^ 2 - a ^ 2) / 2
```

you get

```lean
2 * h = b ^ 2 - a ^ 2
(r - h) * (r + h) = a ^ 4
```

and after factoring

```lean
r - h = α ^ 4
r + h = β ^ 4
a = α * β
```

the new quartic equation is

```lean
b ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4
```

so the witnesses are

```lean
refine ⟨β, α, b, ?_, ?_, ?_⟩
```

The algebraic core inside the copied proof should be this:

```lean
let h : ℤ := (b ^ 2 - a ^ 2) / 2

have htwoh : 2 * h = b ^ 2 - a ^ 2 := by
  -- same parity argument as the main case, using that a,b are odd from B odd
  -- and B = a*b
  exact two_mul_half_diff_of_odd hb ha hB_eq hBodd

have hr_sq : r ^ 2 = h ^ 2 + a ^ 4 := by
  have hsq : (b ^ 2 - a ^ 2) ^ 2 = 4 * h ^ 2 := by
    nlinarith [htwoh]
  have h4 : 4 * r ^ 2 = 4 * (h ^ 2 + a ^ 4) := by
    nlinarith [hsym_id, hsq]
  nlinarith [h4]

have hmul : (r - h) * (r + h) = a ^ 4 := by
  nlinarith [hr_sq]

have hcop_rh : Int.gcd (r - h) (r + h) = 1 := by
  -- same helper as main branch, but using `hra_cop : Int.gcd r a = 1`
  exact coprime_rh hr hr_odd hra_cop htwoh hr_sq

obtain ⟨α, β, hαpos, hβpos, hαβ, hleft, hright⟩ :=
  pos_fourth_of_coprime_mul_fourth ha hmul hcop_rh

have hb_quartic : b ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
  have hdiff : 2 * h = β ^ 4 - α ^ 4 := by
    nlinarith [hleft, hright]
  have ha_sq : a ^ 2 = (α * β) ^ 2 := by
    rw [hαβ]
  nlinarith [htwoh, hdiff, ha_sq]

refine ⟨β, α, b, ?hquartic, ?hnonbase_new, ?hsmaller⟩

 · -- QuarticPlusZ β α b
   -- unfold/simp your definition; the equation is `hb_quartic`.
   simpa [QuarticPlusZ, mul_comm, mul_left_comm, mul_assoc] using hb_quartic

 · -- ¬ BaseZ β α
   -- exactly the copied main-branch nonbase argument.
   -- If `BaseZ β α`, then α = β = 1, hence a = 1 and then hb_quartic gives b = 1,
   -- so B = 1 and the original solution is BaseZ, contradiction.
   exact symmetric_nonbase_from_old hnonbase hB_eq hαβ hb_quartic hαpos hβpos

 · -- α.natAbs < B.natAbs
   have hβ_gt_one : 1 < β := by
     exact beta_gt_one_from_nonbase hnonbase hB_eq hαβ hb_quartic hαpos hβpos
   have hα_lt_a : α < a := by
     -- from `a = α*β`, `0 < α`, and `1 < β`
     nlinarith [hαβ, hαpos, hβ_gt_one]
   have ha_le_B : a ≤ B := by
     rw [hB_eq]
     nlinarith [ha, hb]
   have hα_lt_B : α < B := lt_of_lt_of_le hα_lt_a ha_le_B
   exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hα_lt_B
```

The placeholder names in that last block (`gcd_of_gcd_mul_right_eq_one`, `two_mul_half_diff_of_odd`, `symmetric_nonbase_from_old`, `beta_gt_one_from_nonbase`) are not new mathematics; they are the corresponding pieces already present in your main branch. The essential Lean-level answer is: **yes, copy the proof with `a ↔ b`, but keep `h = (b²-a²)/2`, derive `gcd(r,a)=1`, factor `a⁴`, and return `⟨β, α, b, ...⟩`.**
