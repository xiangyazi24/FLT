# Q2704 (dm-codex1): raw square factors to `EulerSquarePair`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target downstream Lean area: new file importing `N12QuarticEisenstein` and `N12FourSquaresAP`  
Namespace: `MazurProof.RationalPointsN12`

This is self-contained Lean/math design, as requested. I did **not** inspect the unpushed local file. The route is mathematically sound, with one important correction in wording: the constructors do not follow from `RawSqBranchEvenFactors/OddFactors` alone; they also use the branch `IsCoprime m n` and the parity side of the factorization disjunction.

## Audit verdict

### Even raw factors

From

```text
m - n = a^2,
m + n = b^2,
n = 2*c^2,
2*m - n = 2*d^2
```

we get

```text
d^2 = a^2 + c^2,
b^2 = a^2 + 4*c^2.
```

Since `m` is odd and `n` is even, `m-n` is odd, hence `a` is odd. Then `a^2 + c^2 = d^2` forces `d` odd and `4 ∣ c`. If `c = 4*t`, define

```text
E.A = 2*t       -- i.e. c/2, and it is even
E.D = a
E.B = b
E.C = d
```

Then

```text
E.B^2 = b^2 = a^2 + 4*c^2 = a^2 + 16*(2*t)^2 = 16*E.A^2 + E.D^2,
E.C^2 = d^2 = a^2 + c^2 = a^2 + 4*(2*t)^2 = 4*E.A^2 + E.D^2.
```

The `hADcop` field is not automatic from the factor package; it comes from `IsCoprime m n`:

```text
IsCoprime m n
⇒ IsCoprime (m-n) n
⇒ IsCoprime a n
⇒ IsCoprime a c
⇒ IsCoprime (c/2) a.
```

### Odd raw factors

From

```text
m - n = 2*a^2,
m + n = 2*b^2,
n = c^2,
2*m - n = d^2
```

we get

```text
b^2 = a^2 + c^2,
d^2 = 4*a^2 + c^2.
```

Since `n` is odd and `n = c^2`, `c` is odd. Then `c^2 + a^2 = b^2` forces `b` odd and `4 ∣ a`. If `a = 4*t`, define

```text
E.A = 2*t       -- i.e. a/2, and it is even
E.D = c
E.B = d
E.C = b
```

Then

```text
E.B^2 = d^2 = 4*a^2 + c^2 = 16*(2*t)^2 + c^2 = 16*E.A^2 + E.D^2,
E.C^2 = b^2 = a^2 + c^2 = 4*(2*t)^2 + c^2 = 4*E.A^2 + E.D^2.
```

Again, `hADcop` comes from the branch coprimality:

```text
IsCoprime m n
⇒ IsCoprime (m-n) n
⇒ IsCoprime (2*a^2) c^2
⇒ IsCoprime a c
⇒ IsCoprime (a/2) c.
```

## Pasteable Lean for the downstream file

The helper names are prefixed with `q2704_` to avoid collisions with local helpers already added to `N12QuarticEisenstein.lean`.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-! ## 1. No `EulerSquarePair` from strict descent -/

private lemma q2704_natAbs_lt_natAbs_of_pos_lt {x y : ℤ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    x.natAbs < y.natAbs := by
  rcases Int.eq_succ_of_zero_lt hx with ⟨x0, rfl⟩
  rcases Int.eq_succ_of_zero_lt hy with ⟨y0, rfl⟩
  norm_num at hxy ⊢
  exact_mod_cast hxy

/-- A strict descent on the positive product `A*D` rules out existence of any
`EulerSquarePair`. -/
theorem no_eulerSquarePair_of_descent
    (hdesc : EulerSquarePairDescent) :
    ¬ Nonempty EulerSquarePair := by
  rintro ⟨E0⟩
  let P : ℕ → Prop := fun k => ∃ E : EulerSquarePair, k = (E.A * E.D).natAbs
  have hP : ∃ k : ℕ, P k := ⟨(E0.A * E0.D).natAbs, E0, rfl⟩
  let k : ℕ := Nat.find hP
  have hkP : P k := Nat.find_spec hP
  rcases hkP with ⟨E, hkE⟩
  rcases hdesc E with ⟨F, hlt⟩
  have hFmem : P ((F.A * F.D).natAbs) := ⟨F, rfl⟩
  have hmin : k ≤ (F.A * F.D).natAbs := Nat.find_min' hP hFmem
  have hFpos : 0 < F.A * F.D := mul_pos F.hApos F.hDpos
  have hEpos : 0 < E.A * E.D := mul_pos E.hApos E.hDpos
  have hmeasure : (F.A * F.D).natAbs < (E.A * E.D).natAbs :=
    q2704_natAbs_lt_natAbs_of_pos_lt hFpos hEpos hlt
  have hlt_k : (F.A * F.D).natAbs < k := by
    simpa [hkE] using hmeasure
  exact (not_lt_of_ge hmin) hlt_k

/-! ## 2. Parity and mod-8 divisibility helpers -/

private lemma q2704_odd_sub_even {x y : ℤ}
    (hx : Odd x) (hy : Even y) : Odd (x - y) := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

private lemma q2704_odd_of_sq_eq_odd {x y : ℤ}
    (hx : Odd x) (h : x = y ^ 2) : Odd y := by
  rcases Int.even_or_odd y with hyEven | hyOdd
  · exfalso
    rcases hx with ⟨r, hx⟩
    rcases hyEven with ⟨s, hy⟩
    rw [hx, hy] at h
    ring_nf at h
    omega
  · exact hyOdd

/-- In `x^2 + z^2 = y^2`, if `x` is odd then `y` is odd. -/
private lemma q2704_odd_right_of_odd_left_sq_add_sq_eq_sq {x y z : ℤ}
    (hx : Odd x) (h : x ^ 2 + z ^ 2 = y ^ 2) : Odd y := by
  rcases Int.even_or_odd y with hyEven | hyOdd
  · exfalso
    rcases hx with ⟨r, hx⟩
    rcases hyEven with ⟨s, hy⟩
    rcases Int.even_or_odd z with hzEven | hzOdd
    · rcases hzEven with ⟨t, hz⟩
      rw [hx, hy, hz] at h
      ring_nf at h
      omega
    · rcases hzOdd with ⟨t, hz⟩
      rw [hx, hy, hz] at h
      ring_nf at h
      omega
  · exact hyOdd

/-- Robust mod-8 lemma: if `x,y` are odd and `x^2 + z^2 = y^2`, then `4 ∣ z`.

Proof is by parity cases on `z` and on the half of `z`; it avoids depending on
any specialized modular-square API. -/
theorem q2704_four_dvd_of_odd_odd_sq_add_sq_eq_sq {x y z : ℤ}
    (hx : Odd x) (hy : Odd y) (h : x ^ 2 + z ^ 2 = y ^ 2) :
    (4 : ℤ) ∣ z := by
  rcases hx with ⟨r, hx⟩
  rcases hy with ⟨s, hy⟩
  rcases Int.even_or_odd z with hzEven | hzOdd
  · rcases hzEven with ⟨t, hz⟩
    rcases Int.even_or_odd t with htEven | htOdd
    · rcases htEven with ⟨u, ht⟩
      refine ⟨u, ?_⟩
      rw [hz, ht]
      ring
    · exfalso
      rcases htOdd with ⟨u, ht⟩
      rw [hx, hy, hz, ht] at h
      ring_nf at h
      omega
  · exfalso
    rcases hzOdd with ⟨t, hz⟩
    rw [hx, hy, hz] at h
    ring_nf at h
    omega

/-! ## 3. Coprimality helpers for the `hADcop` field -/

private lemma q2704_isCoprime_m_sub_n_n {m n : ℤ}
    (hcop : IsCoprime m n) : IsCoprime (m - n) n := by
  have h0 : IsCoprime (m - (1 : ℤ) * n) n :=
    (IsCoprime.sub_mul_right_left_iff (x := m) (y := n) (z := (1 : ℤ))).2 hcop
  simpa [one_mul] using h0

private lemma q2704_isCoprime_sq_left {x y : ℤ}
    (h : IsCoprime (x ^ 2) y) : IsCoprime x y := by
  have h' : IsCoprime (x * x) y := by
    simpa [pow_two] using h
  exact h'.of_mul_left_left

private lemma q2704_isCoprime_sq_right {x y : ℤ}
    (h : IsCoprime x (y ^ 2)) : IsCoprime x y := by
  have h' : IsCoprime x (y * y) := by
    simpa [pow_two] using h
  exact h'.of_mul_right_left

/-- Even branch coprimality bridge:
`IsCoprime m n`, `m-n=a^2`, `n=2*c^2`, `c=2*A0` imply
`IsCoprime A0 a`. -/
private lemma q2704_isCoprime_A_a_of_even_raw
    {m n a c A0 : ℤ}
    (hcop : IsCoprime m n)
    (hma : m - n = a ^ 2)
    (hnc : n = 2 * c ^ 2)
    (hcA : c = 2 * A0) :
    IsCoprime A0 a := by
  have hmn : IsCoprime (m - n) n := q2704_isCoprime_m_sub_n_n hcop
  have ha_n : IsCoprime a n := by
    apply q2704_isCoprime_sq_left
    simpa [hma] using hmn
  have ha_2c2 : IsCoprime a ((2 : ℤ) * c ^ 2) := by
    simpa [hnc] using ha_n
  have ha_c2 : IsCoprime a (c ^ 2) := ha_2c2.of_mul_right_right
  have ha_c : IsCoprime a c := q2704_isCoprime_sq_right ha_c2
  have hA_dvd_c : A0 ∣ c := ⟨2, by rw [hcA]; ring⟩
  exact ha_c.symm.of_isCoprime_of_dvd_left hA_dvd_c

/-- Odd branch coprimality bridge:
`IsCoprime m n`, `m-n=2*a^2`, `n=c^2`, `a=2*A0` imply
`IsCoprime A0 c`. -/
private lemma q2704_isCoprime_A_c_of_odd_raw
    {m n a c A0 : ℤ}
    (hcop : IsCoprime m n)
    (hma : m - n = 2 * a ^ 2)
    (hnc : n = c ^ 2)
    (haA : a = 2 * A0) :
    IsCoprime A0 c := by
  have hmn : IsCoprime (m - n) n := q2704_isCoprime_m_sub_n_n hcop
  have h2a2_c2 : IsCoprime ((2 : ℤ) * a ^ 2) (c ^ 2) := by
    simpa [hma, hnc] using hmn
  have ha2_c2 : IsCoprime (a ^ 2) (c ^ 2) := h2a2_c2.of_mul_left_right
  have ha_c2 : IsCoprime a (c ^ 2) := q2704_isCoprime_sq_left ha2_c2
  have ha_c : IsCoprime a c := q2704_isCoprime_sq_right ha_c2
  have hA_dvd_a : A0 ∣ a := ⟨2, by rw [haA]; ring⟩
  exact ha_c.of_isCoprime_of_dvd_left hA_dvd_a

/-! ## 4. Algebra extracted from factor packages -/

private lemma q2704_even_core_identities
    {m n a b c d : ℤ}
    (hma : m - n = a ^ 2)
    (hmb : m + n = b ^ 2)
    (hnc : n = 2 * c ^ 2)
    (h2md : 2 * m - n = 2 * d ^ 2) :
    d ^ 2 = a ^ 2 + c ^ 2 ∧ b ^ 2 = a ^ 2 + 4 * c ^ 2 := by
  constructor <;> nlinarith

private lemma q2704_odd_core_identities
    {m n a b c d : ℤ}
    (hma : m - n = 2 * a ^ 2)
    (hmb : m + n = 2 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2md : 2 * m - n = d ^ 2) :
    b ^ 2 = a ^ 2 + c ^ 2 ∧ d ^ 2 = 4 * a ^ 2 + c ^ 2 := by
  constructor <;> nlinarith

/-! ## 5. Constructors from raw factors to `EulerSquarePair` -/

/-- Even raw factors construct an `EulerSquarePair` with
`A = c/2`, `D = a`, `B = b`, `C = d`.  The proof avoids division by writing
`c = 4*t` and setting `A = 2*t`. -/
theorem rawEvenFactors_to_eulerSquarePair
    {X N S m n : ℤ}
    (hbranch : EisensteinSqBranch X N S m n)
    (hnEven : Even n)
    (hf : RawSqBranchEvenFactors m n) :
    Nonempty EulerSquarePair := by
  have hmOdd : Odd m := rawSqBranchMParityStatement hbranch
  rcases hbranch with ⟨hnpos, hnm, hcop, hX, hN, hS⟩
  rcases hf with
    ⟨a, b, c, d, hapos, hbpos, hcpos, hdpos, hma, hmb, hnc, h2md⟩
  have hcore := q2704_even_core_identities hma hmb hnc h2md
  have hdsq : d ^ 2 = a ^ 2 + c ^ 2 := hcore.1
  have hbsq : b ^ 2 = a ^ 2 + 4 * c ^ 2 := hcore.2
  have hmnaOdd : Odd (m - n) := q2704_odd_sub_even hmOdd hnEven
  have haOdd : Odd a := q2704_odd_of_sq_eq_odd hmnaOdd hma
  have hsum : a ^ 2 + c ^ 2 = d ^ 2 := by nlinarith
  have hdOdd : Odd d := q2704_odd_right_of_odd_left_sq_add_sq_eq_sq haOdd hsum
  have hc4 : (4 : ℤ) ∣ c :=
    q2704_four_dvd_of_odd_odd_sq_add_sq_eq_sq haOdd hdOdd hsum
  rcases hc4 with ⟨t, hc4⟩
  let A0 : ℤ := 2 * t
  have hcA : c = 2 * A0 := by
    dsimp [A0]
    rw [hc4]
    ring
  have hA0pos : 0 < A0 := by
    dsimp [A0]
    nlinarith
  have hA0even : Even A0 := by
    refine ⟨t, ?_⟩
    dsimp [A0]
    ring
  have hAD : IsCoprime A0 a :=
    q2704_isCoprime_A_a_of_even_raw hcop hma hnc hcA
  have hBfield : b ^ 2 = 16 * A0 ^ 2 + a ^ 2 := by
    calc
      b ^ 2 = a ^ 2 + 4 * c ^ 2 := hbsq
      _ = 16 * A0 ^ 2 + a ^ 2 := by
        rw [hcA]
        ring
  have hCfield : d ^ 2 = 4 * A0 ^ 2 + a ^ 2 := by
    calc
      d ^ 2 = a ^ 2 + c ^ 2 := hdsq
      _ = 4 * A0 ^ 2 + a ^ 2 := by
        rw [hcA]
        ring
  exact ⟨{
    A := A0
    D := a
    B := b
    C := d
    hApos := hA0pos
    hDpos := hapos
    hDodd := haOdd
    hAeven := hA0even
    hADcop := hAD
    hBpos := hbpos
    hCpos := hdpos
    hB := hBfield
    hC := hCfield }⟩

/-- Odd raw factors construct an `EulerSquarePair` with
`A = a/2`, `D = c`, `B = d`, `C = b`.  The proof avoids division by writing
`a = 4*t` and setting `A = 2*t`. -/
theorem rawOddFactors_to_eulerSquarePair
    {X N S m n : ℤ}
    (hbranch : EisensteinSqBranch X N S m n)
    (hnOdd : Odd n)
    (hf : RawSqBranchOddFactors m n) :
    Nonempty EulerSquarePair := by
  rcases hbranch with ⟨hnpos, hnm, hcop, hX, hN, hS⟩
  rcases hf with
    ⟨a, b, c, d, hapos, hbpos, hcpos, hdpos, hma, hmb, hnc, h2md⟩
  have hcore := q2704_odd_core_identities hma hmb hnc h2md
  have hbsq : b ^ 2 = a ^ 2 + c ^ 2 := hcore.1
  have hdsq : d ^ 2 = 4 * a ^ 2 + c ^ 2 := hcore.2
  have hcOdd : Odd c := q2704_odd_of_sq_eq_odd hnOdd hnc
  have hsum : c ^ 2 + a ^ 2 = b ^ 2 := by nlinarith
  have hbOdd : Odd b := q2704_odd_right_of_odd_left_sq_add_sq_eq_sq hcOdd hsum
  have ha4 : (4 : ℤ) ∣ a :=
    q2704_four_dvd_of_odd_odd_sq_add_sq_eq_sq hcOdd hbOdd hsum
  rcases ha4 with ⟨t, ha4⟩
  let A0 : ℤ := 2 * t
  have haA : a = 2 * A0 := by
    dsimp [A0]
    rw [ha4]
    ring
  have hA0pos : 0 < A0 := by
    dsimp [A0]
    nlinarith
  have hA0even : Even A0 := by
    refine ⟨t, ?_⟩
    dsimp [A0]
    ring
  have hAD : IsCoprime A0 c :=
    q2704_isCoprime_A_c_of_odd_raw hcop hma hnc haA
  have hBfield : d ^ 2 = 16 * A0 ^ 2 + c ^ 2 := by
    calc
      d ^ 2 = 4 * a ^ 2 + c ^ 2 := hdsq
      _ = 16 * A0 ^ 2 + c ^ 2 := by
        rw [haA]
        ring
  have hCfield : b ^ 2 = 4 * A0 ^ 2 + c ^ 2 := by
    calc
      b ^ 2 = a ^ 2 + c ^ 2 := hbsq
      _ = 4 * A0 ^ 2 + c ^ 2 := by
        rw [haA]
        ring
  exact ⟨{
    A := A0
    D := c
    B := d
    C := b
    hApos := hA0pos
    hDpos := hcpos
    hDodd := hcOdd
    hAeven := hA0even
    hADcop := hAD
    hBpos := hdpos
    hCpos := hbpos
    hB := hBfield
    hC := hCfield }⟩

/-! ## 6. Final raw branch contradiction from factor packages -/

/-- Once `eulerSquarePairDescent` is imported, either raw factor package is impossible. -/
theorem rawSqBranchDescentFromFactorsStatement :
    RawSqBranchDescentFromFactorsStatement := by
  intro X N S m n hbranch hfac
  have hno : ¬ Nonempty EulerSquarePair :=
    no_eulerSquarePair_of_descent eulerSquarePairDescent
  apply hno
  rcases hfac with hEven | hOdd
  · exact rawEvenFactors_to_eulerSquarePair hbranch hEven.1 hEven.2
  · exact rawOddFactors_to_eulerSquarePair hbranch hOdd.1 hOdd.2

end MazurProof.RationalPointsN12
```

## Notes if one field fails locally

The most likely local mismatch is not mathematical; it is an API/name mismatch around `IsCoprime` destructors. The exact facts needed for `hADcop` are these two lemmas:

```lean
-- even branch
IsCoprime m n →
m - n = a ^ 2 →
n = 2 * c ^ 2 →
c = 2 * A0 →
IsCoprime A0 a

-- odd branch
IsCoprime m n →
m - n = 2 * a ^ 2 →
n = c ^ 2 →
a = 2 * A0 →
IsCoprime A0 c
```

Both are proved above using only Bezout-coprime monotonicity under divisors and the standard facts
`IsCoprime (x*y) z → IsCoprime x z`, `IsCoprime (x*y) z → IsCoprime y z`, and their right-hand versions.

The other possible local mismatch is `Nat.find` syntax; the proof is intentionally written on the predicate

```lean
P k := ∃ E : EulerSquarePair, k = (E.A * E.D).natAbs
```

so it does not require a custom well-founded relation or quotienting by equality of structures.
