# Q2452-RETRY primitive centered four-square AP normalization

## Verdict

The proposed final reduction statement

```lean
def ArbitraryAP_to_primitive_centered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    Nonempty PrimitiveCenteredFourSqAP
```

is **true as a mathematical normalization target**.  There is no counterexample coming from parity, sign choices, reversal, or gcd division.  After reversing to make the square common difference positive and dividing all four roots by their common root gcd, the normalized roots are automatically odd and pairwise coprime.

However, the strong structure with six pairwise gcd fields and four oddness fields should **not** be the first object constructed from the input.  The Lean-feasible route is:

1. construct a positive primitive AP of four squares using one global root-gcd condition;
2. prove parity and pairwise coprimality as separate lemmas from that weak primitive object;
3. center the AP using `Δ = 4*N`;
4. package the strong `PrimitiveCenteredFourSqAP` at the end.

Sign choices are irrelevant for this normalization layer: squares, `Int.gcd`, `natAbs`, and oddness modulo `2` are unchanged by replacing a root by its negative.  Reversal is only needed to make the common difference positive.

One warning: the `Nonempty PrimitiveCenteredFourSqAP` conclusion forgets provenance.  That is enough if the downstream contradiction is `¬ Nonempty PrimitiveCenteredFourSqAP`.  If later code needs to relate the normalized roots back to the input, use the stronger intermediate theorem carrying the scale and reversal data, then derive this provenance-free theorem by forgetting fields.

---

## Base definitions

A clean statement-layer file can start with only tactic and elementary integer imports.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic

namespace FLT

/-- Four integer squares are in arithmetic progression. -/
def IntFourSqAP (w x y z : ℤ) : Prop :=
  x^2 - w^2 = y^2 - x^2 ∧ y^2 - x^2 = z^2 - y^2

/-- The square AP is constant.  Roots may differ by signs. -/
def FourSqAPConst (w x y z : ℤ) : Prop :=
  w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2

/-- GCD of the four roots, using absolute values. -/
def rootGCD4 (a b c d : ℤ) : ℕ :=
  Nat.gcd a.natAbs (Nat.gcd b.natAbs (Nat.gcd c.natAbs d.natAbs))
```

For construction, use a weak positive primitive object first.

```lean
structure PositivePrimitiveFourSqAP where
  p q r s : ℤ
  Δ : ℤ
  hΔpos : 0 < Δ
  hpq : q^2 - p^2 = Δ
  hqr : r^2 - q^2 = Δ
  hrs : s^2 - r^2 = Δ
  hroot : rootGCD4 p q r s = 1
```

For centering, separate the weak centered object from the final strong package.

```lean
structure WeakPrimitiveCenteredFourSqAP where
  X : ℤ
  N : ℤ
  hNpos : 0 < N
  p q r s : ℤ
  hp : p^2 = X - 6*N
  hq : q^2 = X - 2*N
  hr : r^2 = X + 2*N
  hs : s^2 = X + 6*N
  hroot : rootGCD4 p q r s = 1

structure PrimitiveCenteredFourSqAP extends WeakPrimitiveCenteredFourSqAP where
  hpq_gcd : Int.gcd p q = 1
  hpr_gcd : Int.gcd p r = 1
  hps_gcd : Int.gcd p s = 1
  hqr_gcd : Int.gcd q r = 1
  hqs_gcd : Int.gcd q s = 1
  hrs_gcd : Int.gcd r s = 1
  hp_odd : p % 2 = 1
  hq_odd : q % 2 = 1
  hr_odd : r % 2 = 1
  hs_odd : s % 2 = 1
```

If you want to keep the user-proposed non-extended structure exactly, use the same fields and replace the final `extends` constructor by a direct record constructor.  The mathematics and theorem DAG below are unchanged.

---

## DAG 1: adjacent equality forces constant

This part is purely linear algebra over the square terms and should close with `nlinarith`.

```lean
theorem intFourSqAP_const_of_adjacent_eq
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hzero : w^2 = x^2 ∨ x^2 = y^2 ∨ y^2 = z^2) :
    FourSqAPConst w x y z := by
  unfold IntFourSqAP FourSqAPConst at *
  rcases hAP with ⟨h1, h2⟩
  rcases hzero with h | h | h <;> nlinarith

theorem intFourSqAP_diff_ne_zero_of_nonconst
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    x^2 - w^2 ≠ 0 := by
  intro hdiff
  apply hnonconst
  exact intFourSqAP_const_of_adjacent_eq hAP (Or.inl (by nlinarith))
```

Useful variant if the later branch starts with another adjacent difference:

```lean
theorem intFourSqAP_const_of_common_diff_zero
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hdiff : x^2 - w^2 = 0) :
    FourSqAPConst w x y z := by
  exact intFourSqAP_const_of_adjacent_eq hAP (Or.inl (by nlinarith))
```

Edge case handled here: if the common difference is zero, the four **squares** are constant.  No root sign conclusion is needed.

---

## DAG 2: reverse AP to make positive common difference

```lean
theorem intFourSqAP_reverse
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    IntFourSqAP z y x w := by
  unfold IntFourSqAP at *
  rcases hAP with ⟨h1, h2⟩
  constructor <;> nlinarith
```

Recommended theorem shape:

```lean
theorem intFourSqAP_or_reverse_positive_diff
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    ∃ p q r s Δ : ℤ,
      0 < Δ ∧
      q^2 - p^2 = Δ ∧
      r^2 - q^2 = Δ ∧
      s^2 - r^2 = Δ ∧
      (((p = w ∧ q = x ∧ r = y ∧ s = z) ∧ Δ = x^2 - w^2) ∨
       ((p = z ∧ q = y ∧ r = x ∧ s = w) ∧ Δ = w^2 - x^2)) := by
  classical
  let δ : ℤ := x^2 - w^2
  have hδne : δ ≠ 0 := by
    dsimp [δ]
    exact intFourSqAP_diff_ne_zero_of_nonconst hAP hnonconst
  rcases lt_trichotomy (0 : ℤ) δ with hpos | hzero | hneg
  · refine ⟨w, x, y, z, δ, hpos, ?_, ?_, ?_, Or.inl ?_⟩
    · dsimp [δ]
    · unfold IntFourSqAP at hAP; rcases hAP with ⟨h1, h2⟩; dsimp [δ]; nlinarith
    · unfold IntFourSqAP at hAP; rcases hAP with ⟨h1, h2⟩; dsimp [δ]; nlinarith
    · exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · exact False.elim (hδne hzero.symm)
  · refine ⟨z, y, x, w, -δ, by nlinarith, ?_, ?_, ?_, Or.inr ?_⟩
    · unfold IntFourSqAP at hAP; rcases hAP with ⟨h1, h2⟩; dsimp [δ]; nlinarith
    · unfold IntFourSqAP at hAP; rcases hAP with ⟨h1, h2⟩; dsimp [δ]; nlinarith
    · dsimp [δ]; nlinarith
    · exact ⟨⟨rfl, rfl, rfl, rfl⟩, by dsimp [δ]; ring⟩
```

This is intentionally provenance-carrying.  The final `Nonempty` theorem can forget the last disjunction.

---

## DAG 3: divide by the common root gcd

The exact gcd notion needed is the gcd of the **four roots**, not the gcd of the four square terms and not six pairwise gcds.

Use helper lemmas for `rootGCD4` first:

```lean
theorem rootGCD4_dvd_left (a b c d : ℤ) :
    rootGCD4 a b c d ∣ a.natAbs := by
  unfold rootGCD4
  exact Nat.gcd_dvd_left _ _

theorem rootGCD4_dvd_second (a b c d : ℤ) :
    rootGCD4 a b c d ∣ b.natAbs := by
  unfold rootGCD4
  exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)

theorem rootGCD4_dvd_third (a b c d : ℤ) :
    rootGCD4 a b c d ∣ c.natAbs := by
  unfold rootGCD4
  exact Nat.dvd_trans
    (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))
    (Nat.gcd_dvd_right _ _)

theorem rootGCD4_dvd_fourth (a b c d : ℤ) :
    rootGCD4 a b c d ∣ d.natAbs := by
  unfold rootGCD4
  exact Nat.dvd_trans
    (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_dvd_right _ _)

theorem dvd_rootGCD4 {k : ℕ} {a b c d : ℤ}
    (ha : k ∣ a.natAbs) (hb : k ∣ b.natAbs)
    (hc : k ∣ c.natAbs) (hd : k ∣ d.natAbs) :
    k ∣ rootGCD4 a b c d := by
  unfold rootGCD4
  exact Nat.dvd_gcd ha (Nat.dvd_gcd hb (Nat.dvd_gcd hc hd))
```

The division theorem should expose the scale and the divided difference:

```lean
theorem positive_four_sq_AP_divide_root_gcd
    {a b c d Δ : ℤ}
    (hΔpos : 0 < Δ)
    (hab : b^2 - a^2 = Δ)
    (hbc : c^2 - b^2 = Δ)
    (hcd : d^2 - c^2 = Δ) :
    ∃ g : ℕ, 0 < g ∧
    ∃ p q r s Δ' : ℤ,
      0 < Δ' ∧
      a = (g : ℤ) * p ∧
      b = (g : ℤ) * q ∧
      c = (g : ℤ) * r ∧
      d = (g : ℤ) * s ∧
      Δ = (g : ℤ)^2 * Δ' ∧
      q^2 - p^2 = Δ' ∧
      r^2 - q^2 = Δ' ∧
      s^2 - r^2 = Δ' ∧
      rootGCD4 p q r s = 1 := by
  -- proof outline below
  sorry
```

Implementation outline:

* Let `G := rootGCD4 a b c d`, `g := (G : ℤ)`.
* Prove `0 < G`.  If `G = 0`, then all four `natAbs` values are zero, so all roots are zero; then `Δ = 0`, contradicting `hΔpos`.
* Use `rootGCD4_dvd_*` and `Int.natCast_dvd` / `Int.natAbs_dvd`-style conversions to obtain integer quotients `p q r s` with `a = (G:ℤ)*p`, etc.  In current mathlib, examples of this pattern use `Int.natCast_dvd.mpr` after a natural divisibility fact for `natAbs`.
* After substitution, `hab` gives `Δ = (G:ℤ)^2 * (q^2 - p^2)`.  Define `Δ' := q^2 - p^2`; the other two equations follow by `nlinarith` or `ring_nf` after substitution.
* `0 < Δ'` follows from `Δ = (G:ℤ)^2 * Δ'`, `0 < Δ`, and `0 < (G:ℤ)^2`.
* `rootGCD4 p q r s = 1`: if a natural `k` divides all four quotient `natAbs`s, then `G*k` divides all four original `natAbs`s, so `G*k ∣ G` by `dvd_rootGCD4`; since `G > 0`, cancel to get `k = 1`.  Equivalently prove `rootGCD4 p q r s ∣ 1` and use `Nat.dvd_one.mp`.

Useful APIs in the pinned mathlib style:

```lean
Nat.gcd_dvd_left
Nat.gcd_dvd_right
Nat.dvd_gcd
Nat.dvd_one.mp
Int.gcd_def
Int.natAbs_mul
Int.natAbs_eq_zero
Int.natCast_dvd
Int.ediv_mul_cancel
Int.gcd_eq_gcd_ab
Int.gcd_greatest
```

This is the only bookkeeping-heavy part.  Do not try to prove the pairwise gcd fields during this division step.

---

## DAG 4: parity and divisibility by `4`/`8`

For any four-square AP, the common square residues modulo `4` are constant.  In the primitive case they cannot all be `0`, so all roots are odd.  Then odd squares are `1` modulo `8`, so the primitive common difference is divisible by `8`.

Recommended theorem shape:

```lean
theorem positivePrimitiveFourSqAP_odd_and_dvd8
    (A : PositivePrimitiveFourSqAP) :
    A.p % 2 = 1 ∧ A.q % 2 = 1 ∧ A.r % 2 = 1 ∧ A.s % 2 = 1 ∧
    (8 : ℤ) ∣ A.Δ := by
  -- finite residue proof, preferably with ZMod 4 and ZMod 8 or with omega cases
  sorry
```

Break it into two finite lemmas:

```lean
theorem four_sq_AP_mod4_same
    {p q r s Δ : ℤ}
    (hpq : q^2 - p^2 = Δ)
    (hqr : r^2 - q^2 = Δ)
    (hrs : s^2 - r^2 = Δ) :
    p^2 % 4 = q^2 % 4 ∧
    q^2 % 4 = r^2 % 4 ∧
    r^2 % 4 = s^2 % 4 ∧
    (4 : ℤ) ∣ Δ := by
  -- finite check: square residues mod 4 are only 0 or 1, and a length-4 AP in {0,1}
  -- has step 0 mod 4.
  sorry

theorem odd_sq_sub_dvd8
    {a b Δ : ℤ}
    (ha : a % 2 = 1)
    (hb : b % 2 = 1)
    (hΔ : b^2 - a^2 = Δ) :
    (8 : ℤ) ∣ Δ := by
  -- finite check: odd square is 1 mod 8.
  sorry
```

Proof details for `positivePrimitiveFourSqAP_odd_and_dvd8`:

1. From `four_sq_AP_mod4_same`, all four square residues are equal modulo `4`.
2. If that common residue is `0`, prove all four roots are even.  Then `2 ∣ rootGCD4 p q r s`, contradicting `hroot = 1`.
3. Therefore the common residue is `1`, and every root has `% 2 = 1`.
4. Apply `odd_sq_sub_dvd8` to `q^2 - p^2 = Δ`.

Useful APIs/tactics:

```lean
Int.emod_two_eq_zero_or_one
Int.dvd_of_emod_eq_zero
Int.emod_eq_emod_iff_emod_sub_eq_zero
ZMod
fin_cases
norm_num
omega
```

The statement `p % 2 = 1` is correct even for negative odd roots because Lean's integer remainder modulo a positive integer is nonnegative.

---

## DAG 5: pairwise gcd is derived, not assumed

This is the main edge-case audit.  Pairwise gcd `= 1` is indeed forced by global root gcd plus the four-square AP and oddness.

Recommended theorem shape:

```lean
theorem positivePrimitiveFourSqAP_pairwise_gcd
    (A : PositivePrimitiveFourSqAP)
    (hp_odd : A.p % 2 = 1)
    (hq_odd : A.q % 2 = 1)
    (hr_odd : A.r % 2 = 1)
    (hs_odd : A.s % 2 = 1) :
    Int.gcd A.p A.q = 1 ∧
    Int.gcd A.p A.r = 1 ∧
    Int.gcd A.p A.s = 1 ∧
    Int.gcd A.q A.r = 1 ∧
    Int.gcd A.q A.s = 1 ∧
    Int.gcd A.r A.s = 1 := by
  -- prime divisor argument below
  sorry
```

Prime-divisor proof:

* Adjacent pairs: if an odd prime `ℓ` divides two adjacent roots, then `ℓ ∣ Δ`; the recurrence `next^2 = previous^2 + Δ` forces `ℓ` to divide all four roots.  This contradicts `rootGCD4 = 1`.
* Distance-two pairs: if `ℓ` divides roots two steps apart, then `ℓ ∣ 2*Δ`.  Oddness excludes `ℓ = 2`, so `ℓ ∣ Δ`, and again all roots are forced divisible by `ℓ`.
* Endpoint pair `(p,s)`: if `ℓ ∣ p` and `ℓ ∣ s`, then `ℓ ∣ 3*Δ`.  For `ℓ ≠ 3`, conclude `ℓ ∣ Δ`.  For the exceptional prime `ℓ = 3`, use square residues modulo `3`: from `p ≡ s ≡ 0`, the middle equations give `q^2 ≡ Δ` and `r^2 ≡ -Δ`; if `3 ∤ Δ`, one of `Δ` and `-Δ` is the nonsquare residue modulo `3`, impossible.  Hence `3 ∣ Δ`, and then `q,r` are also divisible by `3`.

This special `ℓ = 3` endpoint case is the only nontrivial edge case in the pairwise proof.  It is why a naive one-line argument from `s^2 - p^2 = 3*Δ` is incomplete.

Useful APIs/patterns:

```lean
Int.isCoprime_iff_gcd_eq_one
Nat.Prime.not_coprime_iff_dvd
Nat.Prime.dvd_of_dvd_mul_left
Nat.Prime.dvd_of_dvd_mul_right
Int.natCast_dvd
Int.dvd_coe_gcd
Int.Prime.dvd_of_dvd_pow'
Nat.prime_two
Nat.prime_three
```

A robust Lean implementation strategy is to prove pairwise coprimality as `IsCoprime A.p A.q` etc., then convert each one with `Int.isCoprime_iff_gcd_eq_one.mp`.

---

## DAG 6: centering

Centering only needs `4 ∣ Δ`; the stronger `8 ∣ Δ` from primitivity is harmless.

```lean
theorem positivePrimitiveFourSqAP_to_weak_centered
    (A : PositivePrimitiveFourSqAP)
    (h4 : (4 : ℤ) ∣ A.Δ) :
    Nonempty WeakPrimitiveCenteredFourSqAP := by
  rcases h4 with ⟨N, hΔN⟩  -- hΔN : A.Δ = 4 * N
  have hNpos : 0 < N := by
    have h4pos : (0 : ℤ) < 4 := by norm_num
    nlinarith [A.hΔpos]
  let X : ℤ := A.p^2 + 6*N
  refine ⟨{
    X := X
    N := N
    hNpos := hNpos
    p := A.p
    q := A.q
    r := A.r
    s := A.s
    hp := ?_
    hq := ?_
    hr := ?_
    hs := ?_
    hroot := A.hroot
  }⟩
  · dsimp [X]; ring
  · dsimp [X]
    have : A.q^2 = A.p^2 + 4*N := by nlinarith [A.hpq]
    nlinarith
  · dsimp [X]
    have hq' : A.q^2 = A.p^2 + 4*N := by nlinarith [A.hpq]
    have hr' : A.r^2 = A.p^2 + 8*N := by nlinarith [A.hqr, hq']
    nlinarith
  · dsimp [X]
    have hq' : A.q^2 = A.p^2 + 4*N := by nlinarith [A.hpq]
    have hr' : A.r^2 = A.p^2 + 8*N := by nlinarith [A.hqr, hq']
    have hs' : A.s^2 = A.p^2 + 12*N := by nlinarith [A.hrs, hr']
    nlinarith
```

The algebra is:

```text
Δ = 4N,
q^2 = p^2 + 4N = (p^2 + 6N) - 2N,
r^2 = p^2 + 8N = (p^2 + 6N) + 2N,
s^2 = p^2 + 12N = (p^2 + 6N) + 6N.
```

Since `0 < Δ = 4N`, `N` is positive.  No sign condition on roots is needed.

---

## Final assembly theorem shapes

First assemble the weak positive primitive AP from arbitrary input:

```lean
theorem arbitraryAP_to_positivePrimitive
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    Nonempty PositivePrimitiveFourSqAP := by
  rcases intFourSqAP_or_reverse_positive_diff hAP hnonconst with
    ⟨a, b, c, d, Δ, hΔpos, hab, hbc, hcd, hprov⟩
  rcases positive_four_sq_AP_divide_root_gcd hΔpos hab hbc hcd with
    ⟨g, hgpos, p, q, r, s, Δ', hΔ'pos, ha, hb, hc, hd, hΔscale,
      hpq, hqr, hrs, hroot⟩
  exact ⟨{
    p := p, q := q, r := r, s := s, Δ := Δ'
    hΔpos := hΔ'pos
    hpq := hpq, hqr := hqr, hrs := hrs
    hroot := hroot
  }⟩
```

Then assemble weak centered:

```lean
theorem arbitraryAP_to_weak_primitive_centered
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    Nonempty WeakPrimitiveCenteredFourSqAP := by
  rcases arbitraryAP_to_positivePrimitive hAP hnonconst with ⟨A⟩
  rcases positivePrimitiveFourSqAP_odd_and_dvd8 A with
    ⟨hpodd, hqodd, hrodd, hsodd, h8⟩
  have h4 : (4 : ℤ) ∣ A.Δ := by
    rcases h8 with ⟨k, hk⟩
    refine ⟨2*k, ?_⟩
    nlinarith
  exact positivePrimitiveFourSqAP_to_weak_centered A h4
```

Finally package the strong object:

```lean
theorem weak_centered_to_positivePrimitive
    (C : WeakPrimitiveCenteredFourSqAP) :
    PositivePrimitiveFourSqAP := by
  refine {
    p := C.p, q := C.q, r := C.r, s := C.s, Δ := 4*C.N
    hΔpos := by nlinarith [C.hNpos]
    hpq := by nlinarith [C.hp, C.hq]
    hqr := by nlinarith [C.hq, C.hr]
    hrs := by nlinarith [C.hr, C.hs]
    hroot := C.hroot
  }

theorem weak_centered_to_strong
    (C : WeakPrimitiveCenteredFourSqAP) :
    Nonempty PrimitiveCenteredFourSqAP := by
  let A := weak_centered_to_positivePrimitive C
  rcases positivePrimitiveFourSqAP_odd_and_dvd8 A with
    ⟨hpodd, hqodd, hrodd, hsodd, h8⟩
  rcases positivePrimitiveFourSqAP_pairwise_gcd A hpodd hqodd hrodd hsodd with
    ⟨hpq, hpr, hps, hqr, hqs, hrs⟩
  exact ⟨{
    C with
    hpq_gcd := hpq
    hpr_gcd := hpr
    hps_gcd := hps
    hqr_gcd := hqr
    hqs_gcd := hqs
    hrs_gcd := hrs
    hp_odd := hpodd
    hq_odd := hqodd
    hr_odd := hrodd
    hs_odd := hsodd
  }⟩

theorem arbitraryAP_to_primitive_centered
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    Nonempty PrimitiveCenteredFourSqAP := by
  rcases arbitraryAP_to_weak_primitive_centered hAP hnonconst with ⟨C⟩
  exact weak_centered_to_strong C
```

If the public API must be the `Prop` alias exactly:

```lean
def ArbitraryAP_to_primitive_centered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    Nonempty PrimitiveCenteredFourSqAP

theorem arbitraryAP_to_primitive_centered_prop :
    ArbitraryAP_to_primitive_centered := by
  intro w x y z hAP hnonconst
  exact arbitraryAP_to_primitive_centered hAP hnonconst
```

---

## Edge-case audit summary

1. **Adjacent equality**: if any adjacent square equality holds, the AP is constant by `nlinarith`.  This excludes zero common difference.
2. **Negative common difference**: reverse `(w,x,y,z)` to `(z,y,x,w)`.  The AP condition is preserved and the common difference changes sign.
3. **Root gcd division**: divide by `rootGCD4`, the gcd of the four root absolute values.  This is the exact primitive notion needed.  Pairwise gcds are not appropriate at this stage.
4. **Gcd nonzero**: positive common difference implies not all roots are zero, hence `0 < rootGCD4`.
5. **Divided common difference**: if each root is divisible by `g`, then each square difference is divisible by `g^2`; define the new difference after division.
6. **Parity**: modulo `4`, a length-four AP of square residues must have step `0`; in the primitive case the common residue cannot be `0`, or all roots would be even and `2 ∣ rootGCD4`.  Thus all roots are odd, and then `8 ∣ Δ`.
7. **Pairwise gcds**: all six pairwise gcds are forced by the global root gcd plus oddness.  The endpoint pair has a real `3`-prime exception that must be handled by a mod-`3` square-residue argument.
8. **Centering**: with `Δ = 4N`, set `X = p^2 + 6N`.  Then the four square equations are exactly `X - 6N`, `X - 2N`, `X + 2N`, `X + 6N`, and `N > 0` follows from `Δ > 0`.

Bottom line: the original strong `PrimitiveCenteredFourSqAP` conditions are achievable; the corrected Lean design is to introduce a weak/global-gcd primitive layer and derive oddness plus pairwise coprimality before constructing the strong centered record.

end FLT
