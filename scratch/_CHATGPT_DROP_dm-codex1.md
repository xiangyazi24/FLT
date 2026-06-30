# Q2431-RETRY2 denominator clearing code

Use this as a standalone Lean block.  The denominator construction uses the product of the four reduced denominators, so each scaled coordinate is explicitly integral.

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-- Four integer squares in arithmetic progression, written as equal first differences. -/
def IntFourSqAP (a b c d : ℤ) : Prop :=
  b^2 - a^2 = c^2 - b^2 ∧ c^2 - b^2 = d^2 - c^2

/-- A common nonzero integer scaling of four rationals to four integers. -/
structure RatIntScale4 (w x y z : ℚ) where
  M : ℤ
  hM : M ≠ 0
  W X Y Z : ℤ
  hW : (W : ℚ) = (M : ℚ) * w
  hX : (X : ℚ) = (M : ℚ) * x
  hY : (Y : ℚ) = (M : ℚ) * y
  hZ : (Z : ℚ) = (M : ℚ) * z

private lemma rat_scale_by_four_den_product
    (q r s t : ℚ) :
    (((q.num * (r.den : ℤ) * (s.den : ℤ) * (t.den : ℤ) : ℤ) : ℚ)
      = ((((q.den * r.den * s.den * t.den : ℕ) : ℤ) : ℚ) * q)) := by
  calc
    (((q.num * (r.den : ℤ) * (s.den : ℤ) * (t.den : ℤ) : ℤ) : ℚ)
        = (q.num : ℚ) * (r.den : ℚ) * (s.den : ℚ) * (t.den : ℚ) := by
          norm_cast
    _ = ((q.den : ℚ) * q) * (r.den : ℚ) * (s.den : ℚ) * (t.den : ℚ) := by
          rw [← Rat.den_mul_eq_num q]
    _ = ((((q.den * r.den * s.den * t.den : ℕ) : ℤ) : ℚ) * q) := by
          norm_cast
          ring

theorem rat_int_scale4_exists (w x y z : ℚ) : ∃ s : RatIntScale4 w x y z := by
  refine ⟨
    { M := ((w.den * x.den * y.den * z.den : ℕ) : ℤ)
      hM := by
        exact Int.ofNat_ne_zero.2
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero (Rat.den_ne_zero w) (Rat.den_ne_zero x))
              (Rat.den_ne_zero y))
            (Rat.den_ne_zero z))
      W := w.num * (x.den : ℤ) * (y.den : ℤ) * (z.den : ℤ)
      X := x.num * (w.den : ℤ) * (y.den : ℤ) * (z.den : ℤ)
      Y := y.num * (w.den : ℤ) * (x.den : ℤ) * (z.den : ℤ)
      Z := z.num * (w.den : ℤ) * (x.den : ℤ) * (y.den : ℤ)
      hW := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product w x y z
      hX := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product x w y z
      hY := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product y w x z
      hZ := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product z w x y }⟩

private lemma ratIntScale4_sq_sub_cast
    {A B M : ℤ} {a b : ℚ}
    (hA : (A : ℚ) = (M : ℚ) * a)
    (hB : (B : ℚ) = (M : ℚ) * b) :
    ((A^2 - B^2 : ℤ) : ℚ) = (M : ℚ)^2 * (a^2 - b^2) := by
  calc
    ((A^2 - B^2 : ℤ) : ℚ) = (A : ℚ)^2 - (B : ℚ)^2 := by
      norm_cast
    _ = ((M : ℚ) * a)^2 - ((M : ℚ) * b)^2 := by
      rw [hA, hB]
    _ = (M : ℚ)^2 * (a^2 - b^2) := by
      ring

theorem intFourSqAP_of_ratIntScale4
    {w x y z : ℚ} (s : RatIntScale4 w x y z)
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    IntFourSqAP s.W s.X s.Y s.Z := by
  constructor
  · apply Rat.intCast_injective
    calc
      ((s.X^2 - s.W^2 : ℤ) : ℚ)
          = (s.M : ℚ)^2 * (x^2 - w^2) := by
            exact ratIntScale4_sq_sub_cast s.hX s.hW
      _ = (s.M : ℚ)^2 * (y^2 - x^2) := by
            rw [h1]
      _ = ((s.Y^2 - s.X^2 : ℤ) : ℚ) := by
            exact (ratIntScale4_sq_sub_cast s.hY s.hX).symm
  · apply Rat.intCast_injective
    calc
      ((s.Y^2 - s.X^2 : ℤ) : ℚ)
          = (s.M : ℚ)^2 * (y^2 - x^2) := by
            exact ratIntScale4_sq_sub_cast s.hY s.hX
      _ = (s.M : ℚ)^2 * (z^2 - y^2) := by
            rw [h2]
      _ = ((s.Z^2 - s.Y^2 : ℤ) : ℚ) := by
            exact (ratIntScale4_sq_sub_cast s.hZ s.hY).symm
```

Proof strategy encoded above:

1. Set `M = w.den * x.den * y.den * z.den`, cast to `ℤ`.
2. Set each scaled integer by multiplying the numerator by the other three denominators.
3. Prove each scaling identity with `Rat.den_mul_eq_num`, `norm_cast`, and `ring`.
4. For AP transport, cast the desired integer equality to `ℚ`, rewrite each square difference as `M^2` times the rational square difference, use `h1`/`h2`, and conclude by `Rat.intCast_injective`.
