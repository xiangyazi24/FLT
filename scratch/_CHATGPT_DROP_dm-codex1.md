# Q2452 primitive centered four-square AP normalization

## Verdict

The intended normalization is mathematically correct, but the proposed structure is **too strong for the first construction step**.  After reversing, dividing by the common gcd of the four roots, and centering, one can indeed derive:

* positive common difference;
* common difference divisible by `4` (in fact by `8` once roots are odd);
* all primitive roots odd;
* pairwise coprimality of the primitive roots.

However, for Lean this should be built in two layers:

1. construct a **weak primitive centered AP** with a single global root-gcd condition;
2. prove parity and pairwise-coprime lemmas from that weak object;
3. package the strong `PrimitiveCenteredFourSqAP` only after those lemmas are available.

There is no genuine counterexample to the proposed strong conditions.  The issue is proof engineering: pairwise `Int.gcd p q = 1` fields are awkward to construct directly during gcd division.  They should be derived from a global root gcd plus AP equations.

---

## Recommended definitions

Keep the public AP predicates:

```lean
import Mathlib.Tactic
import Mathlib.NumberTheory.PythagoreanTriples

def IntFourSqAP (w x y z : ℤ) : Prop :=
  x^2 - w^2 = y^2 - x^2 ∧ y^2 - x^2 = z^2 - y^2

def FourSqAPConst (w x y z : ℤ) : Prop :=
  w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

Use a global root gcd for the first normalization layer:

```lean
def rootGCD4 (a b c d : ℤ) : ℕ :=
  Nat.gcd a.natAbs (Nat.gcd b.natAbs (Nat.gcd c.natAbs d.natAbs))

structure WeakPrimitiveCenteredFourSqAP where
  X : ℤ
  N : ℤ
  hNpos : 0 < N
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  hp : p^2 = X - 6*N
  hq : q^2 = X - 2*N
  hr : r^2 = X + 2*N
  hs : s^2 = X + 6*N
  hroot : rootGCD4 p q r s = 1
```

Then define the strong structure as a derived package:

```lean
structure PrimitiveCenteredFourSqAP extends WeakPrimitiveCenteredFourSqAP where
  hpq : Int.gcd p q = 1
  hpr : Int.gcd p r = 1
  hps : Int.gcd p s = 1
  hqr : Int.gcd q r = 1
  hqs : Int.gcd q s = 1
  hrs : Int.gcd r s = 1
  hp_odd : p % 2 = 1
  hq_odd : q % 2 = 1
  hr_odd : r % 2 = 1
  hs_odd : s % 2 = 1
```

This is the clean theorem target:

```lean
def ArbitraryAP_to_weak_primitive_centered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    Nonempty WeakPrimitiveCenteredFourSqAP

def WeakPrimitiveCentered_to_strong : Prop :=
  ∀ S : WeakPrimitiveCenteredFourSqAP,
    Nonempty PrimitiveCenteredFourSqAP

def ArbitraryAP_to_primitive_centered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    Nonempty PrimitiveCenteredFourSqAP
```

Then the final wrapper is tiny:

```lean
theorem ArbitraryAP_to_primitive_centered_of_weak
    (hweak : ArbitraryAP_to_weak_primitive_centered)
    (hstrong : WeakPrimitiveCentered_to_strong) :
    ArbitraryAP_to_primitive_centered := by
  intro w x y z hAP hnonconst
  rcases hweak hAP hnonconst with ⟨S⟩
  exact hstrong S
```

---

## DAG step 1: adjacent equality forces constant

This is compile-ready and should close with `nlinarith`.

```lean
theorem intFourSqAP_const_of_adjacent_eq
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hzero : w^2 = x^2 ∨ x^2 = y^2 ∨ y^2 = z^2) :
    FourSqAPConst w x y z := by
  unfold IntFourSqAP FourSqAPConst at *
  rcases hAP with ⟨h1, h2⟩
  rcases hzero with h | h | h <;> nlinarith
```

Useful companion:

```lean
theorem intFourSqAP_nonconst_commonDiff_ne_zero
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    x^2 - w^2 ≠ 0 := by
  intro h
  apply hnonconst
  apply intFourSqAP_const_of_adjacent_eq hAP
  left
  nlinarith
```

---

## DAG step 2: reverse AP to make positive common difference

```lean
theorem intFourSqAP_reverse
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    IntFourSqAP z y x w := by
  unfold IntFourSqAP at *
  rcases hAP with ⟨h1, h2⟩
  constructor <;> nlinarith
```

Recommended normalized theorem shape:

```lean
def AP_or_reversed_positive_diff : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    ∃ p q r s Δ : ℤ,
      0 < Δ ∧
      q^2 - p^2 = Δ ∧
      r^2 - q^2 = Δ ∧
      s^2 - r^2 = Δ ∧
      ((p = w ∧ q = x ∧ r = y ∧ s = z) ∨
       (p = z ∧ q = y ∧ r = x ∧ s = w))
```

Proof: set `δ = x^2 - w^2`; if `0 < δ`, use original order; if `δ < 0`, use reversed order; `δ ≠ 0` follows from the previous step.  This is `lt_trichotomy` plus `nlinarith`.

---

## DAG step 3: divide by the common root gcd

Use `rootGCD4`, not six pairwise gcds, for the division step.

The exact theorem should be:

```lean
def RootGCD4Division : Prop :=
  ∀ {w x y z Δ : ℤ},
    0 < Δ →
    x^2 - w^2 = Δ →
    y^2 - x^2 = Δ →
    z^2 - y^2 = Δ →
    ∃ g p q r s Δ' : ℤ,
      0 < g ∧ 0 < Δ' ∧
      w = g*p ∧ x = g*q ∧ y = g*r ∧ z = g*s ∧
      q^2 - p^2 = Δ' ∧
      r^2 - q^2 = Δ' ∧
      s^2 - r^2 = Δ' ∧
      rootGCD4 p q r s = 1
```

Implementation route:

```lean
let G : ℕ := rootGCD4 w x y z
let g : ℤ := (G : ℤ)
```

Key facts:

* `G ≠ 0`: because `Δ > 0` implies not all roots are zero.
* `G ∣ w.natAbs`, `G ∣ x.natAbs`, `G ∣ y.natAbs`, `G ∣ z.natAbs` by repeated `Nat.gcd_dvd_left/right`.
* Convert those to integer divisibility and choose quotients `p q r s`.
* `g^2 ∣ Δ` because `Δ = x^2 - w^2` and both `x,w` are multiples of `g`.
* Set `Δ' = Δ / g^2` and prove the new AP equations by `ring` after substituting `w = g*p`, etc.
* `rootGCD4 p q r s = 1`: if a natural `d` divides all four quotients, then `G*d` divides all four original roots, contradicting maximality of `G` unless `d=1`.

Useful APIs:

```lean
Nat.gcd_dvd_left
Nat.gcd_dvd_right
Nat.dvd_gcd
Int.natAbs_mul
Int.natAbs_eq_zero
Int.natAbs_dvd
Int.dvd_natAbs
Int.ofNat_dvd
Int.natCast_dvd_natCast
Int.ediv_mul_cancel
mul_pos
pow_pos
```

This is gcd bookkeeping; it is not `ring`/`nlinarith` only.

---

## DAG step 4: parity and divisibility by 4/8

The primitive parity theorem should be stated for the weak normalized roots.

```lean
def WeakPrimitiveAPParity : Prop :=
  ∀ {p q r s Δ : ℤ},
    q^2 - p^2 = Δ →
    r^2 - q^2 = Δ →
    s^2 - r^2 = Δ →
    rootGCD4 p q r s = 1 →
    p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1 ∧ s % 2 = 1 ∧ 8 ∣ Δ
```

Why true:

1. Squares mod `4` are only `0` or `1`.
2. A length-four arithmetic progression in `{0,1}` modulo `4` must be constant modulo `4`; otherwise one of the four residues is `2` or `3`.
3. Hence `p^2,q^2,r^2,s^2` have the same residue mod `4`, and `4 ∣ Δ`.
4. If the common square residue is `0`, then all roots are even, contradicting `rootGCD4 p q r s = 1`.
5. Therefore all roots are odd, i.e. `% 2 = 1` in Lean's nonnegative remainder convention.
6. Odd squares are `1 mod 8`, hence `8 ∣ Δ`.

Useful implementation options:

* Use `ZMod 4` / `ZMod 8` and `fin_cases`, or
* use integer `%` with `omega`/`omega`-style finite case splits.

Useful APIs:

```lean
Int.emod_two_eq_zero_or_one
Int.dvd_of_emod_eq_zero
Int.emod_eq_emod_iff_emod_sub_eq_zero
ZMod
Fin
fin_cases
omega
```

For a low-friction proof, I recommend two finite residue lemmas:

```lean
def four_sq_AP_mod4_constant_residue : Prop :=
  ∀ {a b c d δ : ℤ},
    b^2 - a^2 = δ → c^2 - b^2 = δ → d^2 - c^2 = δ →
    a^2 % 4 = b^2 % 4 ∧ b^2 % 4 = c^2 % 4 ∧ c^2 % 4 = d^2 % 4

def odd_sq_diff_dvd8 : Prop :=
  ∀ {a b δ : ℤ},
    a % 2 = 1 → b % 2 = 1 → b^2 - a^2 = δ → 8 ∣ δ
```

The first is a finite mod-4 check.  The second is a finite mod-8 check.

---

## DAG step 5: derive pairwise coprimality from weak primitive data

This is true, but should be a separate theorem rather than a constructor obligation during gcd division.

```lean
def WeakPrimitiveAPPairwise : Prop :=
  ∀ {p q r s Δ : ℤ},
    q^2 - p^2 = Δ →
    r^2 - q^2 = Δ →
    s^2 - r^2 = Δ →
    rootGCD4 p q r s = 1 →
    p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
    Int.gcd p q = 1 ∧
    Int.gcd p r = 1 ∧
    Int.gcd p s = 1 ∧
    Int.gcd q r = 1 ∧
    Int.gcd q s = 1 ∧
    Int.gcd r s = 1
```

Proof idea by prime divisors:

* If an odd prime `ℓ` divides two roots at distance `1`, then `ℓ ∣ Δ`, hence `ℓ` divides all four square terms and all four roots, contradicting `rootGCD4 = 1`.
* If the distance is `2`, then `ℓ ∣ 2*Δ`; since roots are odd, `ℓ ≠ 2`, so `ℓ ∣ Δ`, and again `ℓ` divides all roots.
* If the distance is `3`, then `ℓ ∣ 3*Δ`.  If `ℓ ≠ 3`, conclude `ℓ ∣ Δ`.  If `ℓ = 3`, use square residues mod `3`: from endpoints divisible by `3`, both middle terms force `Δ` and `2*Δ` to be quadratic residues mod `3`; this is impossible unless `3 ∣ Δ`.  Then all four roots are divisible by `3`, contradiction.

Useful APIs:

```lean
Nat.Prime
Nat.Prime.dvd_of_dvd_mul_left
Nat.Prime.dvd_of_dvd_mul_right
Nat.Prime.not_dvd_one
Nat.dvd_gcd
Int.natAbs_dvd_natAbs
Int.dvd_natAbs
Int.ofNat_dvd
Int.gcd_eq_zero_iff
Int.isCoprime_iff_gcd_eq_one
```

For Lean, it may be easier to prove pairwise as `Nat.Coprime p.natAbs q.natAbs` first, then convert to `Int.gcd p q = 1`.

---

## DAG step 6: centering

Once the primitive positive AP has common difference `Δ > 0` and `4 ∣ Δ`, centering is pure algebra.

```lean
def PositivePrimitiveAP_to_centered_weak : Prop :=
  ∀ {p q r s Δ : ℤ},
    0 < Δ →
    q^2 - p^2 = Δ →
    r^2 - q^2 = Δ →
    s^2 - r^2 = Δ →
    rootGCD4 p q r s = 1 →
    4 ∣ Δ →
    Nonempty WeakPrimitiveCenteredFourSqAP
```

Proof skeleton:

```lean
intro p q r s Δ hΔpos hpq hqr hrs hroot h4
rcases h4 with ⟨N, hΔ⟩       -- Δ = 4*N, or maybe Δ = N*4 depending on rcases orientation
have hNpos : 0 < N := by nlinarith
let X : ℤ := p^2 + 6*N
refine ⟨{
  X := X
  N := N
  hNpos := hNpos
  p := p
  q := q
  r := r
  s := s
  hp := by dsimp [X]; ring
  hq := by dsimp [X]; nlinarith
  hr := by dsimp [X]; nlinarith
  hs := by dsimp [X]; nlinarith
  hroot := hroot
}⟩
```

The identities are:

```text
q^2 = p^2 + 4N = (p^2 + 6N) - 2N,
r^2 = p^2 + 8N = (p^2 + 6N) + 2N,
s^2 = p^2 + 12N = (p^2 + 6N) + 6N.
```

All of this is `ring`/`nlinarith`.

---

## Final theorem assembly

A good implementation target is:

```lean
def ArbitraryAP_to_weak_primitive_centered_DAG : Prop :=
  AP_or_reversed_positive_diff →
  RootGCD4Division →
  WeakPrimitiveAPParity →
  PositivePrimitiveAP_to_centered_weak →
  ArbitraryAP_to_weak_primitive_centered

def WeakPrimitiveCentered_to_strong_DAG : Prop :=
  WeakPrimitiveAPParity →
  WeakPrimitiveAPPairwise →
  WeakPrimitiveCentered_to_strong
```

The strong final statement requested by the user is then:

```lean
def ArbitraryAP_to_primitive_centered_DAG : Prop :=
  ArbitraryAP_to_weak_primitive_centered_DAG →
  WeakPrimitiveCentered_to_strong_DAG →
  ArbitraryAP_to_primitive_centered
```

In actual Lean, implement the named theorem bodies rather than these `Prop` aliases, but these statement shapes isolate the hard parts cleanly.

---

## Edge-case audit

1. **Adjacent equality.**  If any of `w^2=x^2`, `x^2=y^2`, or `y^2=z^2` holds, the AP is constant by `nlinarith`.
2. **Negative common difference.**  Reverse the quadruple.  Squares are unchanged and AP remains valid with positive difference.
3. **All zero / all constant.**  Excluded by `¬ FourSqAPConst`; also needed to ensure the root gcd is nonzero.
4. **Zero among primitive roots.**  Impossible after parity: primitive roots are odd.  Before parity, a zero root would be even; mod-4 AP forces all roots even, contradicting `rootGCD4=1`.
5. **Nonprimitive scaling.**  Divide the roots by `rootGCD4`; square differences divide by its square.  Constantness lifts back through multiplication by `g^2`.
6. **Pairwise gcd.**  Pairwise gcd `=1` is achievable, but it is a derived consequence of global root gcd plus AP plus parity.  Do not make it part of the first normalization constructor.

Bottom line: `ArbitraryAP_to_primitive_centered` is true with the proposed strong structure, but the Lean-feasible route should prove `ArbitraryAP_to_weak_primitive_centered` first and then derive the strong pairwise/odd fields separately.
