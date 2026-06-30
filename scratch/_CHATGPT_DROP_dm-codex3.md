# Q2419 drop: normalization layer for four rational squares in AP

Goal:

```lean
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

This drop is only the **normalization layer**.  It does not use elliptic curves, E1/E24 finite-point input, or any Euler descent.  The intended hard theorem remains the primitive integer theorem:

```lean
def IntFourSquaresAPPrimitiveConst : Prop :=
  ∀ {a b c d : ℤ}, IntPrimitive4 a b c d → IntFourSqAP a b c d →
    a^2 = b^2 ∧ b^2 = c^2 ∧ c^2 = d^2
```

The low-level plan is:

```text
rational AP
  -> clear root denominators to an integer-root AP
  -> divide by common gcd of the four integer roots
  -> apply primitive integer theorem
  -> scale equality of squares back to rationals.
```

---

## 1. Mathlib APIs to use

Useful rational APIs found in Mathlib:

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

#check Rat.num
#check Rat.den
#check Rat.pos                 -- 0 < q.den
#check Rat.den_ne_zero         -- q.den ≠ 0
#check Rat.mkRat_num_den'      -- Rat.mkRat q.num q.den = q
#check Rat.pow_eq_divInt       -- q^n as Rat.divInt (q.num^n) (q.den^n)
#check Rat.intCast_injective   -- Function.Injective (Int.cast : ℤ → ℚ)
#check Rat.forall              -- quantify rationals as integer numerator/denominator
#check Rat.exists
```

Useful denominator/divisibility lemmas if you choose expression-denominator clearing rather than root-denominator clearing:

```lean
#check Rat.add_den_dvd
#check Rat.sub_den_dvd
#check Rat.mul_den_dvd
#check Rat.mul_self_num
#check Rat.mul_self_den
```

Useful integer gcd APIs:

```lean
#check Int.gcd_def
#check Int.gcd_div
#check Int.gcd_div_gcd_div_gcd
#check Int.exists_gcd_one
#check Int.gcd_eq_gcd_ab
```

For the four-root common gcd, the most direct route is still to define the gcd on `natAbs`:

```lean
def rootGcd4 (a b c d : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs) d.natAbs
```

Then use the usual `Nat.gcd` divisibility lemmas (`Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, `Nat.dvd_gcd`) plus `Int.gcd_def`/`natAbs` conversions.  If you instead use iterated `Int.gcd`, `Int.gcd_div` and `Int.gcd_div_gcd_div_gcd` avoid some manual quotient-gcd algebra.

---

## 2. Core definitions

Use the user-facing definitions, plus a nonprimitive integer theorem as a derived target.

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace FLT.Mazur.N12.FourSquaresAPNorm

noncomputable section

/-- Integer roots whose squares form a 4-term arithmetic progression. -/
def IntFourSqAP (a b c d : ℤ) : Prop :=
  b^2 - a^2 = c^2 - b^2 ∧
  c^2 - b^2 = d^2 - c^2

/-- Common-root primitive condition. -/
def IntPrimitive4 (a b c d : ℤ) : Prop :=
  Nat.gcd (Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs) d.natAbs = 1

/-- Hard primitive theorem; this is where Euler/Fermat descent belongs. -/
def IntFourSquaresAPPrimitiveConst : Prop :=
  ∀ {a b c d : ℤ}, IntPrimitive4 a b c d → IntFourSqAP a b c d →
    a^2 = b^2 ∧ b^2 = c^2 ∧ c^2 = d^2

/-- Desired rational theorem. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

---

## 3. A. Rational root denominator clearing

Do **not** write mixed equations like `W = M*w`.  The corrected cast shape is:

```lean
(W : ℚ) = (M : ℚ) * w
```

Package common denominator clearing as a structure:

```lean
/-- Integer representatives of four rationals after multiplying all four roots by
one nonzero integer multiplier. -/
structure RatIntScale4 (w x y z : ℚ) where
  M : ℤ
  hM : M ≠ 0
  W X Y Z : ℤ
  hW : (W : ℚ) = (M : ℚ) * w
  hX : (X : ℚ) = (M : ℚ) * x
  hY : (Y : ℚ) = (M : ℚ) * y
  hZ : (Z : ℚ) = (M : ℚ) * z
```

Recommended helper lemma for each rational:

```lean
/-- A small helper worth proving once from `Rat.mkRat_num_den'`. -/
theorem rat_den_mul_self_eq_num (q : ℚ) :
    ((q.den : ℤ) : ℚ) * q = (q.num : ℚ) := by
  -- Proof plan:
  --   `Rat.mkRat_num_den' q` gives `Rat.mkRat q.num q.den = q`.
  --   Rewrite `Rat.mkRat` using `Rat.mkRat_eq_divInt` / `Rat.divInt`.
  --   Then field-simplify using `Rat.den_ne_zero q`.
  -- In local Lean, this usually closes with:
  --   rw [← Rat.mkRat_num_den' q, Rat.mkRat_eq_divInt]
  --   field_simp [Rat.den_ne_zero]
  --   ring
  -- If the exact simp names differ, prove the equivalent lemma via `Rat.pow_eq_divInt`.
  sorry
```

The theorem target for denominator clearing:

```lean
/-- Root denominator clearing.  A concrete construction is:

```text
M = w.den * x.den * y.den * z.den,
W = w.num * x.den * y.den * z.den,
X = x.num * w.den * y.den * z.den,
Y = y.num * w.den * x.den * z.den,
Z = z.num * w.den * x.den * y.den.
```

Here all denominators are cast through `ℕ -> ℤ` as needed.
-/
theorem rat_int_scale4_exists (w x y z : ℚ) :
    ∃ s : RatIntScale4 w x y z := by
  -- Proof plan:
  --   refine the explicit construction above.
  --   `hM` follows from positivity/nonzero of each `Rat.den`.
  --   each scale identity follows from `rat_den_mul_self_eq_num` and commutative ring algebra.
  -- This is root-level denominator clearing only; no AP equations are used.
  sorry
```

Once the structure is available, transporting AP equations to integer equations is pure algebra and should compile with only cast/ring tuning:

```lean
/-- A scaled rational AP gives an integer-root AP. -/
theorem intFourSqAP_of_ratIntScale4
    {w x y z : ℚ} (s : RatIntScale4 w x y z)
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    IntFourSqAP s.W s.X s.Y s.Z := by
  constructor
  · apply Rat.intCast_injective
    calc
      ((s.X^2 - s.W^2 : ℤ) : ℚ)
          = (s.X : ℚ)^2 - (s.W : ℚ)^2 := by
              push_cast; ring
      _ = (s.M : ℚ)^2 * (x^2 - w^2) := by
              rw [s.hX, s.hW]
              ring
      _ = (s.M : ℚ)^2 * (y^2 - x^2) := by
              rw [h1]
      _ = (s.Y : ℚ)^2 - (s.X : ℚ)^2 := by
              rw [s.hY, s.hX]
              ring
      _ = ((s.Y^2 - s.X^2 : ℤ) : ℚ) := by
              push_cast; ring
  · apply Rat.intCast_injective
    calc
      ((s.Y^2 - s.X^2 : ℤ) : ℚ)
          = (s.Y : ℚ)^2 - (s.X : ℚ)^2 := by
              push_cast; ring
      _ = (s.M : ℚ)^2 * (y^2 - x^2) := by
              rw [s.hY, s.hX]
              ring
      _ = (s.M : ℚ)^2 * (z^2 - y^2) := by
              rw [h2]
      _ = (s.Z : ℚ)^2 - (s.Y : ℚ)^2 := by
              rw [s.hZ, s.hY]
              ring
      _ = ((s.Z^2 - s.Y^2 : ℤ) : ℚ) := by
              push_cast; ring
```

The requested `rat_four_sq_AP_to_int` should include a nonzero-gap preservation clause, but the final constant-case wrapper does not actually need nonzero gap.

```lean
/-- Rational AP to integer AP.  The nonzero-gap clause is useful for contradiction
proofs but is not needed for the total constant-case theorem. -/
theorem rat_four_sq_AP_to_int
    {w x y z : ℚ}
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    ∃ s : RatIntScale4 w x y z,
      IntFourSqAP s.W s.X s.Y s.Z ∧
      (x^2 - w^2 ≠ 0 → s.X^2 - s.W^2 ≠ 0) := by
  rcases rat_int_scale4_exists w x y z with ⟨s⟩
  refine ⟨s, intFourSqAP_of_ratIntScale4 s h1 h2, ?_⟩
  intro hgap hIntGap
  apply hgap
  have hMq : (s.M : ℚ) ≠ 0 := by exact_mod_cast s.hM
  have hM2 : (s.M : ℚ)^2 ≠ 0 := pow_ne_zero 2 hMq
  have hscaled : (s.M : ℚ)^2 * (x^2 - w^2) = 0 := by
    calc
      (s.M : ℚ)^2 * (x^2 - w^2)
          = (s.X : ℚ)^2 - (s.W : ℚ)^2 := by
              rw [s.hX, s.hW]
              ring
      _ = ((s.X^2 - s.W^2 : ℤ) : ℚ) := by
              push_cast; ring
      _ = 0 := by
              rw [hIntGap]
              norm_num
  exact mul_eq_zero.mp hscaled |>.resolve_left hM2
```

If `mul_eq_zero.mp ... |>.resolve_left` syntax is inconvenient, replace the final line by:

```lean
  rcases mul_eq_zero.mp hscaled with hMzero | hgapzero
  · exact (hM2 hMzero).elim
  · exact hgapzero
```

---

## 4. B. Primitive reduction of an integer AP

The cleanest theorem target is a reduction theorem that either the tuple is already constant, or it has a primitive quotient carrying the same AP equations.

```lean
/-- Common gcd of four integer roots. -/
def rootGcd4 (a b c d : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs) d.natAbs

/-- Primitive reduction target.  This is the exact statement the normalization
layer needs; it contains no Euler descent. -/
theorem int_four_sq_AP_primitive_reduction
    {a b c d : ℤ} (hAP : IntFourSqAP a b c d) :
    (a^2 = b^2 ∧ b^2 = c^2 ∧ c^2 = d^2) ∨
    ∃ A B C D g : ℤ,
      g ≠ 0 ∧
      IntPrimitive4 A B C D ∧
      IntFourSqAP A B C D ∧
      a = g*A ∧ b = g*B ∧ c = g*C ∧ d = g*D := by
  -- No-sorry proof plan:
  -- 1. Let `Gnat := rootGcd4 a b c d`.
  -- 2. If `Gnat = 0`, nested `Nat.gcd_eq_zero_iff` gives
  --    `a.natAbs = b.natAbs = c.natAbs = d.natAbs = 0`, hence all roots are zero.
  --    Return the left constant branch.
  -- 3. If `Gnat ≠ 0`, set `g : ℤ := Gnat`.
  -- 4. Prove `g ∣ a`, `g ∣ b`, `g ∣ c`, `g ∣ d` from the nested gcd divisibility lemmas.
  --    Then define `A := a / g`, `B := b / g`, `C := c / g`, `D := d / g`.
  -- 5. Prove the reconstruction equations `a = g*A`, etc. using `Int.ediv_mul_cancel`.
  -- 6. Prove `IntPrimitive4 A B C D`.
  --    Recommended route:
  --      * either use Nat gcd quotient lemmas on `natAbs`, or
  --      * switch temporarily to iterated `Int.gcd` and use `Int.gcd_div` and
  --        `Int.gcd_div_gcd_div_gcd`, then translate back with `Int.gcd_def`.
  -- 7. Prove `IntFourSqAP A B C D` by substituting `a=g*A`, etc. into `hAP`.
  --    Both AP equations become `g^2 * lhs = g^2 * rhs`; cancel `g^2` using
  --    `mul_left_cancel₀ (pow_ne_zero 2 hg)`.
  -- 8. Return the right branch.
  sorry
```

This reduction theorem is not the hard descent; it is gcd bookkeeping and scaling.  It is longer than the final wrapper, but fully elementary.

From this theorem, the nonprimitive integer constant theorem is a short wrapper:

```lean
theorem int_four_sq_AP_const_of_primitive
    (hPrim : IntFourSquaresAPPrimitiveConst) :
    ∀ {a b c d : ℤ}, IntFourSqAP a b c d →
      a^2 = b^2 ∧ b^2 = c^2 ∧ c^2 = d^2 := by
  intro a b c d hAP
  rcases int_four_sq_AP_primitive_reduction hAP with hconst | hred
  · exact hconst
  · rcases hred with ⟨A, B, C, D, g, hg, hprim, hAPprim, ha, hb, hc, hd⟩
    have hconstPrim := hPrim hprim hAPprim
    rcases hconstPrim with ⟨hAB, hBC, hCD⟩
    constructor
    · nlinarith [ha, hb, hAB]
    constructor
    · nlinarith [hb, hc, hBC]
    · nlinarith [hc, hd, hCD]
```

---

## 5. C. Constant-case wrapper: rational from primitive integer theorem

Once the two normalization theorems above exist, the final wrapper is small and contains no number-theoretic descent.

```lean
theorem fourRatSquaresAPConst_of_int
    (hPrim : IntFourSquaresAPPrimitiveConst) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  rcases rat_four_sq_AP_to_int h1 h2 with ⟨s, hAPint, _hgap⟩
  have hIntConst := int_four_sq_AP_const_of_primitive hPrim hAPint
  rcases hIntConst with ⟨hWX, hXY, hYZ⟩

  have hMq : (s.M : ℚ) ≠ 0 := by exact_mod_cast s.hM
  have hM2 : (s.M : ℚ)^2 ≠ 0 := pow_ne_zero 2 hMq

  have hwx_scaled : (s.M : ℚ)^2 * w^2 = (s.M : ℚ)^2 * x^2 := by
    calc
      (s.M : ℚ)^2 * w^2 = ((s.M : ℚ) * w)^2 := by ring
      _ = (s.W : ℚ)^2 := by rw [← s.hW]
      _ = (s.X : ℚ)^2 := by exact_mod_cast hWX
      _ = ((s.M : ℚ) * x)^2 := by rw [s.hX]
      _ = (s.M : ℚ)^2 * x^2 := by ring

  have hxy_scaled : (s.M : ℚ)^2 * x^2 = (s.M : ℚ)^2 * y^2 := by
    calc
      (s.M : ℚ)^2 * x^2 = ((s.M : ℚ) * x)^2 := by ring
      _ = (s.X : ℚ)^2 := by rw [← s.hX]
      _ = (s.Y : ℚ)^2 := by exact_mod_cast hXY
      _ = ((s.M : ℚ) * y)^2 := by rw [s.hY]
      _ = (s.M : ℚ)^2 * y^2 := by ring

  have hyz_scaled : (s.M : ℚ)^2 * y^2 = (s.M : ℚ)^2 * z^2 := by
    calc
      (s.M : ℚ)^2 * y^2 = ((s.M : ℚ) * y)^2 := by ring
      _ = (s.Y : ℚ)^2 := by rw [← s.hY]
      _ = (s.Z : ℚ)^2 := by exact_mod_cast hYZ
      _ = ((s.M : ℚ) * z)^2 := by rw [s.hZ]
      _ = (s.M : ℚ)^2 * z^2 := by ring

  exact ⟨mul_left_cancel₀ hM2 hwx_scaled,
         mul_left_cancel₀ hM2 hxy_scaled,
         mul_left_cancel₀ hM2 hyz_scaled⟩
```

This is the key wrapper requested in part C.  It should compile after the two normalization theorem targets are implemented:

```lean
rat_four_sq_AP_to_int
int_four_sq_AP_primitive_reduction
```

Neither theorem uses Euler descent or elliptic-curve input.

---

## 6. Suggested implementation order

1. Add the definitions:

```lean
IntFourSqAP
IntPrimitive4
IntFourSquaresAPPrimitiveConst
FourRatSquaresAPConst
RatIntScale4
rootGcd4
```

2. Prove rational scaling helpers:

```lean
rat_den_mul_self_eq_num
rat_int_scale4_exists
intFourSqAP_of_ratIntScale4
rat_four_sq_AP_to_int
```

3. Prove gcd primitive reduction:

```lean
int_four_sq_AP_primitive_reduction
int_four_sq_AP_const_of_primitive
```

4. Add the final rational wrapper:

```lean
fourRatSquaresAPConst_of_int
```

This leaves exactly one true mathematical input:

```lean
IntFourSquaresAPPrimitiveConst
```

Everything else is denominator clearing, gcd normalization, and scaling algebra.

```lean
end
end FLT.Mazur.N12.FourSquaresAPNorm
```
