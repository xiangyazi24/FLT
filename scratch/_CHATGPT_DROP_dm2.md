# Q311 (dm2): EDS nonvanishing by specialization

## Recommended path

Use the specialization

```text
(b, c, d) = (2, 3, 2).
```

For Mathlib's `normEDS`, this specialization is the identity sequence:

```lean
normEDS (2 : ℤ) 3 2 j = j
```

for every `j : ℤ`. Therefore, if `j ≠ 0`, the universal polynomial

```lean
normEDS B C D j ∈ ℤ[B,C,D]
```

is nonzero, because evaluation at `B ↦ 2`, `C ↦ 3`, `D ↦ 2` sends it to `j ≠ 0`.

This is Approach (a), but with a much simpler specialization than a genuine elliptic curve. It is degenerate as an elliptic-curve specialization, but that is irrelevant: to prove a universal polynomial is nonzero, any ring homomorphism to any ring under which it has nonzero image is enough.

The important consequence is that Ward's theorem can be made unconditional without proving a Mordell-Weil/non-torsion theorem or a curve-to-EDS dictionary.

---

## Why `(2,3,2)` works

The identity sequence `W j = j` has

```text
W(0)=0,  W(1)=1,  W(2)=2,  W(3)=3,  W(4)=4 = 2*2.
```

Thus it has Mathlib/Ward parameters

```text
b = 2,  c = 3,  d = 2.
```

It also satisfies the adjacent normalized EDS recurrences used to define `normEDS`:

```text
(2*m) * 2
  = (m-1)^2*m*(m+2) - (m-2)*m*(m+1)^2,

2*m + 1
  = (m+2)*m^3 - (m-1)*(m+1)^3.
```

Those are just polynomial identities. Hence `normEDS (2 : ℤ) 3 2` is forced by `normEDSRec` to equal the identity sequence.

The Somos recurrence also checks directly:

```text
(m+2)(m-2) = 4(m+1)(m-1) - 3m^2.
```

---

## Lean proof of the integer specialization

This is the core Lean lemma. It uses only the current EDS API: `normEDSRec`, `normEDS_even`, `normEDS_odd`, and `normEDS_neg`.

```lean
import Mathlib

noncomputable section

lemma normEDS_232_nat (n : ℕ) :
    normEDS (2 : ℤ) 3 2 (n : ℤ) = (n : ℤ) := by
  induction n using normEDSRec with
  | zero =>
      simp
  | one =>
      simp
  | two =>
      simp
  | three =>
      simp
  | four =>
      norm_num
  | even m h1 h2 h3 h4 h5 =>
      let t : ℤ := (m : ℤ) + 3
      have H1 : normEDS (2 : ℤ) 3 2 (t - 2) = t - 2 := by
        convert h1 using 1 <;> dsimp [t] <;> omega
      have H2 : normEDS (2 : ℤ) 3 2 (t - 1) = t - 1 := by
        convert h2 using 1 <;> dsimp [t] <;> omega
      have H3 : normEDS (2 : ℤ) 3 2 t = t := by
        convert h3 using 1 <;> dsimp [t] <;> omega
      have H4 : normEDS (2 : ℤ) 3 2 (t + 1) = t + 1 := by
        convert h4 using 1 <;> dsimp [t] <;> omega
      have H5 : normEDS (2 : ℤ) 3 2 (t + 2) = t + 2 := by
        convert h5 using 1 <;> dsimp [t] <;> omega
      have he := normEDS_even (b := (2 : ℤ)) (c := 3) (d := 2) t
      have hmul :
          normEDS (2 : ℤ) 3 2 (2 * t) * 2 = (2 * t) * 2 := by
        calc
          normEDS (2 : ℤ) 3 2 (2 * t) * 2
              = (t - 1) ^ 2 * t * (t + 2) -
                  (t - 2) * t * (t + 1) ^ 2 := by
                    simpa [H1, H2, H3, H4, H5] using he
          _ = (2 * t) * 2 := by
                    ring
      have hcast : ((2 * (m + 3) : ℕ) : ℤ) = 2 * t := by
        dsimp [t]
        omega
      rw [hcast]
      nlinarith [hmul]
  | odd m h1 h2 h3 h4 =>
      let t : ℤ := (m : ℤ) + 2
      have H1 : normEDS (2 : ℤ) 3 2 (t - 1) = t - 1 := by
        convert h1 using 1 <;> dsimp [t] <;> omega
      have H2 : normEDS (2 : ℤ) 3 2 t = t := by
        convert h2 using 1 <;> dsimp [t] <;> omega
      have H3 : normEDS (2 : ℤ) 3 2 (t + 1) = t + 1 := by
        convert h3 using 1 <;> dsimp [t] <;> omega
      have H4 : normEDS (2 : ℤ) 3 2 (t + 2) = t + 2 := by
        convert h4 using 1 <;> dsimp [t] <;> omega
      have ho := normEDS_odd (b := (2 : ℤ)) (c := 3) (d := 2) t
      have hcast : ((2 * (m + 2) + 1 : ℕ) : ℤ) = 2 * t + 1 := by
        dsimp [t]
        omega
      rw [hcast]
      calc
        normEDS (2 : ℤ) 3 2 (2 * t + 1)
            = (t + 2) * t ^ 3 - (t - 1) * (t + 1) ^ 3 := by
                simpa [H1, H2, H3, H4] using ho
        _ = 2 * t + 1 := by
                ring

lemma normEDS_232_int (j : ℤ) :
    normEDS (2 : ℤ) 3 2 j = j := by
  induction j using Int.negInduction with
  | nat n =>
      exact normEDS_232_nat n
  | neg ih n =>
      simp [normEDS_neg, normEDS_232_nat]
```

If the final `Int.negInduction` branch is brittle under a local Mathlib version, replace it by a constructor split on `j` and use `normEDS_neg`; the mathematical content is only oddness of `normEDS`:

```lean
-- Alternative shape if desired:
-- cases j with
-- | ofNat n => exact normEDS_232_nat n
-- | negSucc n =>
--     simp [Int.negSucc_eq, normEDS_neg, normEDS_232_nat]
```

---

## Universal nonvanishing in `ℤ[B,C,D]`

Here is a self-contained version using `MvPolynomial (Fin 3) ℤ` for the universal ring.

```lean
import Mathlib

noncomputable section

namespace Q311

abbrev U : Type := MvPolynomial (Fin 3) ℤ

abbrev B : U := MvPolynomial.X (0 : Fin 3)
abbrev C : U := MvPolynomial.X (1 : Fin 3)
abbrev D : U := MvPolynomial.X (2 : Fin 3)

abbrev univW (j : ℤ) : U :=
  normEDS B C D j

abbrev val232 : Fin 3 → ℤ :=
  ![2, 3, 2]

abbrev eval232 : U →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) val232

@[simp] lemma eval232_B : eval232 B = 2 := by
  simp [eval232, val232, B]

@[simp] lemma eval232_C : eval232 C = 3 := by
  simp [eval232, val232, C]

@[simp] lemma eval232_D : eval232 D = 2 := by
  simp [eval232, val232, D]

@[simp] lemma eval232_univW (j : ℤ) :
    eval232 (univW j) = normEDS (2 : ℤ) 3 2 j := by
  simp [univW]

theorem univW_ne_zero {j : ℤ} (hj : j ≠ 0) :
    univW j ≠ 0 := by
  intro hzero
  have hmap : eval232 (univW j) = 0 := by
    simpa [hzero]
  have : j = 0 := by
    calc
      j = normEDS (2 : ℤ) 3 2 j := (normEDS_232_int j).symm
      _ = eval232 (univW j) := (eval232_univW j).symm
      _ = 0 := hmap
  exact hj this

theorem universal_normEDS_ne_zero {j : ℤ} (hj : j ≠ 0) :
    normEDS (MvPolynomial.X (0 : Fin 3) : U)
      (MvPolynomial.X (1 : Fin 3) : U)
      (MvPolynomial.X (2 : Fin 3) : U) j ≠ 0 := by
  simpa [univW, B, C, D] using univW_ne_zero (j := j) hj

end Q311
```

The essential lemma behind the last theorem is the trivial ring-hom argument:

```lean
lemma ne_zero_of_map_ne_zero
    {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) {x : A} (hx : f x ≠ 0) : x ≠ 0 := by
  intro hx0
  exact hx (by simp [hx0])
```

I wrote the proof inline above rather than using this helper, because the inline version leaves the evaluated value `j` visible.

---

## Answers to the three questions

### 1. A genuine elliptic-curve specialization

Yes, the classical curve suggested in the prompt works:

```text
E : y^2 + y = x^3 - x,
P = (0,0).
```

For the long Weierstrass model

```text
y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6
```

this has

```text
a1 = 0,  a2 = 0,  a3 = 1,  a4 = -1,  a6 = 0.
```

The standard invariants are

```text
b2 = a1^2 + 4*a2 = 0,
b4 = 2*a4 + a1*a3 = -2,
b6 = a3^2 + 4*a6 = 1,
b8 = a1^2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3^2 - a4^2 = -1.
```

At `P=(0,0)`, the standard division-polynomial values are

```text
ψ2(P) = 2*y + a1*x + a3 = 1,
ψ3(P) = 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8 = -1.
```

The reduced fourth value, i.e. the factor `ψ4/ψ2`, is

```text
2*x^6 + b2*x^5 + 5*b4*x^4 + 10*b6*x^3 + 10*b8*x^2
  + (b2*b8 - b4*b6)*x + (b4*b8 - b6^2),
```

which evaluates to

```text
b4*b8 - b6^2 = (-2)*(-1) - 1 = 1.
```

Thus, in Mathlib's `normEDS` parametrization, where

```lean
normEDS b c d 2 = b
normEDS b c d 3 = c
normEDS b c d 4 = d * b
```

the curve-point example corresponds to

```text
(b,c,d) = (1,-1,1).
```

The usual mathematical proof that all terms are nonzero is:

```text
ψ_n(P)=0  ⇔  [n]P = O,
```

and `P` is non-torsion. One elementary non-torsion proof is by good reduction: for this curve, the reductions at `3` and `5` have respectively `7` and `8` points; torsion over `ℚ` injects into both good reductions, so the rational torsion order divides `gcd(7,8)=1`. Hence rational torsion is trivial, and `P ≠ O` is non-torsion.

This is mathematically clean but not the Lean path I recommend.

### 2. Most Lean-tractable proof

The most Lean-tractable proof is not the curve proof, not a primitive-divisor theorem, and not a valuation argument. It is the direct identity-specialization proof above.

It requires only:

```lean
#check normEDSRec
#check normEDS_even
#check normEDS_odd
#check normEDS_neg
#check map_normEDS
#check MvPolynomial.eval₂Hom
#check MvPolynomial.X
```

plus ordinary tactics:

```lean
ring
norm_num
omega
nlinarith
simp
```

It does **not** require:

```text
Mordell-Weil,
Lutz-Nagell,
finite-field reduction of elliptic curves,
division-polynomial vanishing criteria,
primitive divisors,
valuation theory,
or `normEDS_isEllSequence`.
```

This is a major advantage: current Mathlib's EDS file defines `IsEllSequence` and `normEDS`, and gives the even/odd recurrences and map lemma, but the fully general theorem that `normEDS` satisfies `IsEllDivSequence` is still listed as missing/TODO. The direct proof above avoids that missing theorem.

### 3. Simpler non-curve specialization

Yes. The specialization `(2,3,2)` is the simplest one.

If one insists on a polynomial-family specialization rather than an integer specialization, use for example

```text
(b,c,d) = (2, 3 + T, 2) ∈ ℤ[T].
```

Every term is nonzero in `ℤ[T]`, because evaluating `T ↦ 0` gives the already-proved nonzero integer value `j`. This gives a one-parameter family whose nonvanishing still reduces to the identity specialization.

But for the universal nonvanishing theorem, even that is unnecessary. The direct integer evaluation

```text
B ↦ 2, C ↦ 3, D ↦ 2
```

is already sufficient.

---

## Final recommendation

Implement the two lemmas

```lean
normEDS_232_int : ∀ j : ℤ, normEDS (2 : ℤ) 3 2 j = j
universal_normEDS_ne_zero : ∀ {j : ℤ}, j ≠ 0 → normEDS B C D j ≠ 0
```

and use `universal_normEDS_ne_zero` wherever Ward's theorem needs the unconditional nonvanishing of the universal `normEDS` term.

Do **not** spend effort formalizing the curve `y^2+y=x^3-x` or the non-torsion point `(0,0)` for this specific purpose. That route is mathematically fine, but it requires APIs and theorems far beyond what the EDS nonvanishing argument actually needs.
