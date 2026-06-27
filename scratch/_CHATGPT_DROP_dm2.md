# Q1317 (dm2/dm3): first half of `quartic_plus` descent in Lean 4

## Important correction before the Lean code

As stated, the requested local claims cannot all be proved from the theorem hypotheses exactly as written.

The equation is invariant under `s ↦ -s`.  For the known trivial solution

```text
r = 1, B = 1, s = -1
```

we get

```text
U = 2*r^2 + B^2 - 2*s = 5,
V = 2*r^2 + B^2 + 2*s = 1,
```

so `U < V` is false.  You must either add `0 < s`, or define the descent factors using `t = |s|`.

Also, `U` and `V` are odd immediately only in the odd-`B` branch: since

```text
U ≡ V ≡ B^2  mod 2.
```

So the clean first-half descent step below is the normalized branch with extra local hypotheses

```lean
(hBodd : Odd B) (hs : 0 < s)
```

If you want the original theorem, first replace `s` by `|s|` and split/prove the parity branch for `B` separately.

## Lean code: first-half scaffold

This is the shape I recommend putting into the local file.  The product, oddness, positivity, and `U < V` pieces are written out.  The two genuinely arithmetic seams are isolated as named lemmas:

1. `quarticPlus_gcd_UV_eq_one`: the common-divisor calculation.
2. `coprime_factorization_5_fourth`: the coprime factorization of `5 * B^4`.

Those are exactly the next local lemmas to fill; everything around them is the first-half descent scaffold.

```lean
import Mathlib

namespace QuarticPlusFirstHalf

/-- The quartic-plus equation. -/
def Qeq (r B s : ℤ) : Prop :=
  s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/-- First descent factor. -/
def Udef (r B s : ℤ) : ℤ :=
  2 * r ^ 2 + B ^ 2 - 2 * s

/-- Second descent factor. -/
def Vdef (r B s : ℤ) : ℤ :=
  2 * r ^ 2 + B ^ 2 + 2 * s

/-- The data produced by the first half of the descent. -/
structure FirstHalfData (r B s : ℤ) : Prop where
  U : ℤ
  V : ℤ
  hU_def : U = Udef r B s
  hV_def : V = Vdef r B s
  hprod : U * V = 5 * B ^ 4
  hgcd : Int.gcd U V = 1
  hUodd : Odd U
  hVodd : Odd V
  hUpos : 0 < U
  hUVlt : U < V
  hfactor :
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ a * b = B ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4))

/-- Product identity:

`(2r^2+B^2-2s)(2r^2+B^2+2s) = 5B^4`.
-/
lemma quarticPlus_U_mul_V
    {r B s : ℤ} (hEq : Qeq r B s) :
    Udef r B s * Vdef r B s = 5 * B ^ 4 := by
  unfold Qeq at hEq
  unfold Udef Vdef
  calc
    (2 * r ^ 2 + B ^ 2 - 2 * s) * (2 * r ^ 2 + B ^ 2 + 2 * s)
        = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by
          ring
    _ = 5 * B ^ 4 := by
          rw [show (2 * s) ^ 2 = 4 * s ^ 2 by ring, hEq]
          ring

lemma quarticPlus_U_odd_of_B_odd
    {r B s : ℤ} (hBodd : Odd B) :
    Odd (Udef r B s) := by
  rcases hBodd with ⟨k, hk⟩
  refine ⟨r ^ 2 + 2 * k ^ 2 + 2 * k - s, ?_⟩
  unfold Udef
  rw [hk]
  ring

lemma quarticPlus_V_odd_of_B_odd
    {r B s : ℤ} (hBodd : Odd B) :
    Odd (Vdef r B s) := by
  rcases hBodd with ⟨k, hk⟩
  refine ⟨r ^ 2 + 2 * k ^ 2 + 2 * k + s, ?_⟩
  unfold Vdef
  rw [hk]
  ring

lemma quarticPlus_V_pos
    {r B s : ℤ} (hr : 0 < r) (hB : 0 < B) (hs : 0 < s) :
    0 < Vdef r B s := by
  unfold Vdef
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero r (ne_of_gt hr)
  have hB2 : 0 < B ^ 2 := sq_pos_of_ne_zero B (ne_of_gt hB)
  nlinarith

lemma quarticPlus_U_lt_V
    {r B s : ℤ} (hs : 0 < s) :
    Udef r B s < Vdef r B s := by
  unfold Udef Vdef
  nlinarith

lemma quarticPlus_U_pos_of_product
    {r B s : ℤ} (hB : 0 < B)
    (hprod : Udef r B s * Vdef r B s = 5 * B ^ 4)
    (hVpos : 0 < Vdef r B s) :
    0 < Udef r B s := by
  have hB4 : 0 < B ^ 4 := pow_pos hB 4
  have hprodpos : 0 < Udef r B s * Vdef r B s := by
    rw [hprod]
    nlinarith
  exact pos_of_mul_pos_right hprodpos (le_of_lt hVpos)

/-- The common-divisor seam.

Mathematical proof sketch:

* A common divisor of `U` and `V` divides `V-U = 4s` and `U+V = 2(2r^2+B^2)`.
* Since `U,V` are odd, the common divisor has no factor `2`.
* Any odd prime common divisor divides `U*V = 5B^4`.
* If it divides `B`, then from `U+V ≡ 4r^2 (mod p)` it divides `r`, contradicting
  `gcd r B = 1`.
* The remaining possible prime is `5`; the same argument rules it out when `5 ∣ B`,
  and otherwise `25 ∤ 5B^4` rules out both `U,V` being divisible by `5`.

This is the lemma to fill after the first-half scaffold is in place.
-/
lemma quarticPlus_gcd_UV_eq_one
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hBodd : Odd B)
    (hcop : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    Int.gcd (Udef r B s) (Vdef r B s) = 1 := by
  -- This is the arithmetic seam described above.
  -- It is intentionally isolated so the descent scaffold below is clean.
  sorry

/-- Coprime factorization of `5 * B^4`.

Given positive coprime factors `U,V` with product `5 * B^4`, exactly one side carries
an exponent-one factor `5`; every other prime exponent is a multiple of `4`.  Thus one
factor is a fourth power and the other is `5` times a fourth power.

This should be proved from `Nat.factorization`/`Int.natAbs`, or by transporting to
positive naturals and using prime-factor exponents.
-/
lemma coprime_factorization_5_fourth
    {U V B : ℤ}
    (hB : 0 < B) (hU : 0 < U) (hV : 0 < V)
    (hprod : U * V = 5 * B ^ 4)
    (hcop : Int.gcd U V = 1) :
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ a * b = B ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  -- Prime-factorization seam.  This is where the first-half descent stops.
  sorry

/-- The normalized first-half descent step.

This is the part you want inside the strong-induction step, after replacing `s` by `|s|`
if necessary and after entering the odd-`B` branch.
-/
theorem quarticPlus_firstHalf_step
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hBodd : Odd B) (hs : 0 < s)
    (hcop : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    FirstHalfData r B s := by
  classical
  let U : ℤ := Udef r B s
  let V : ℤ := Vdef r B s

  have hprod : U * V = 5 * B ^ 4 := by
    dsimp [U, V]
    exact quarticPlus_U_mul_V hEq

  have hUodd : Odd U := by
    dsimp [U]
    exact quarticPlus_U_odd_of_B_odd hBodd

  have hVodd : Odd V := by
    dsimp [V]
    exact quarticPlus_V_odd_of_B_odd hBodd

  have hVpos : 0 < V := by
    dsimp [V]
    exact quarticPlus_V_pos hr hB hs

  have hUpos : 0 < U := by
    dsimp [U, V] at hprod hVpos ⊢
    exact quarticPlus_U_pos_of_product hB hprod hVpos

  have hUVlt : U < V := by
    dsimp [U, V]
    exact quarticPlus_U_lt_V hs

  have hgcd : Int.gcd U V = 1 := by
    dsimp [U, V]
    exact quarticPlus_gcd_UV_eq_one hr hB hBodd hcop hEq

  have hfactor :
      ∃ a b : ℤ,
        0 < a ∧ 0 < b ∧ a * b = B ∧
          ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
           (U = 5 * a ^ 4 ∧ V = b ^ 4)) :=
    coprime_factorization_5_fourth hB hUpos hVpos hprod hgcd

  exact
    { U := U
      V := V
      hU_def := rfl
      hV_def := rfl
      hprod := hprod
      hgcd := hgcd
      hUodd := hUodd
      hVodd := hVodd
      hUpos := hUpos
      hUVlt := hUVlt
      hfactor := hfactor }

/-- Strong-induction wrapper on `B.natAbs`.

The induction hypothesis is not used in the first-half algebraic extraction; it becomes
relevant only after `hfactor`, when one constructs the smaller solution.
-/
def FirstHalfGoalAt (n : ℕ) : Prop :=
  ∀ r B s : ℤ,
    B.natAbs = n →
    0 < r → 0 < B → Odd B → 0 < s →
    Int.gcd r B = 1 → Qeq r B s →
    FirstHalfData r B s

theorem quarticPlus_firstHalf_strong_induction :
    ∀ n : ℕ, FirstHalfGoalAt n := by
  intro n
  refine Nat.strongRecOn n ?step
  intro n IH
  intro r B s hBn hr hB hBodd hs hcop hEq
  -- `IH` will be used only in the second half, after constructing the smaller `B'`.
  exact quarticPlus_firstHalf_step hr hB hBodd hs hcop hEq

end QuarticPlusFirstHalf
```

## How to plug this into the original theorem

For the original theorem with arbitrary `s`, do **not** try to prove `U < V` using `s` directly.  Normalize first:

```lean
let t : ℤ := |s|
have ht_nonneg : 0 ≤ t := by
  dsimp [t]
  exact abs_nonneg s
```

Then prove `Qeq r B t` from `Qeq r B s` using `t^2 = s^2`.  After ruling out `t = 0`, call the first-half step with `s := t`.

The even-`B` branch should also be separated before using the `Odd B` lemmas above.  The displayed `quarticPlus_firstHalf_step` is the odd normalized branch; it is the branch in which the classical `U,V` factorization is exactly the clean one requested.
