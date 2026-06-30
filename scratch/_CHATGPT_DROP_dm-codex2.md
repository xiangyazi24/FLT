# Q2491 RootGCD4Division Lean route

The GitHub `main` branch did not contain `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean` at the requested path, so this is written against exactly the definitions in the prompt.  The theorem is true as stated.  The clean proof is to choose

```lean
g = (rootGCD4 w x y z : ℤ),
p = w / g, q = x / g, r = y / g, s = z / g,
Δ' = Δ / g^2.
```

The only real bookkeeping is proving that the quotient tuple is primitive.  The helper `rootGCD4_eq_one_of_common_factor` below proves that if a positive natural `g` is exactly the four-root gcd and all four entries are `g` times signed quotients, then the signed quotient tuple has `rootGCD4 = 1`.

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-- Integer four-square arithmetic progression, in square-difference form. -/
def IntFourSqAP (w x y z : ℤ) : Prop :=
  x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 ∧ y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2

/-- Constant four-square progression. -/
def FourSqAPConst (w x y z : ℤ) : Prop :=
  w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- GCD of the four signed roots, implemented as a natural gcd of absolute values. -/
def rootGCD4 (a b c d : ℤ) : ℕ :=
  Nat.gcd a.natAbs (Nat.gcd b.natAbs (Nat.gcd c.natAbs d.natAbs))

/-- Primitive normalization residual for a nonconstant four-square AP. -/
def RootGCD4Division : Prop :=
  ∀ {w x y z Δ : ℤ},
    0 < Δ →
    x ^ 2 - w ^ 2 = Δ →
    y ^ 2 - x ^ 2 = Δ →
    z ^ 2 - y ^ 2 = Δ →
      ∃ g p q r s Δ' : ℤ,
        0 < g ∧ 0 < Δ' ∧
        w = g * p ∧ x = g * q ∧ y = g * r ∧ z = g * s ∧
        q ^ 2 - p ^ 2 = Δ' ∧
        r ^ 2 - q ^ 2 = Δ' ∧
        s ^ 2 - r ^ 2 = Δ' ∧
        rootGCD4 p q r s = 1

/-- The four-root gcd divides the first absolute value. -/
theorem rootGCD4_dvd_natAbs_w (w x y z : ℤ) :
    rootGCD4 w x y z ∣ w.natAbs := by
  dsimp [rootGCD4]
  exact Nat.gcd_dvd_left _ _

/-- The four-root gcd divides the second absolute value. -/
theorem rootGCD4_dvd_natAbs_x (w x y z : ℤ) :
    rootGCD4 w x y z ∣ x.natAbs := by
  dsimp [rootGCD4]
  exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)

/-- The four-root gcd divides the third absolute value. -/
theorem rootGCD4_dvd_natAbs_y (w x y z : ℤ) :
    rootGCD4 w x y z ∣ y.natAbs := by
  dsimp [rootGCD4]
  have h1 :
      Nat.gcd w.natAbs (Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs)) ∣
        Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs) :=
    Nat.gcd_dvd_right _ _
  have h2 : Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs) ∣
      Nat.gcd y.natAbs z.natAbs :=
    Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd y.natAbs z.natAbs ∣ y.natAbs :=
    Nat.gcd_dvd_left _ _
  exact h1.trans (h2.trans h3)

/-- The four-root gcd divides the fourth absolute value. -/
theorem rootGCD4_dvd_natAbs_z (w x y z : ℤ) :
    rootGCD4 w x y z ∣ z.natAbs := by
  dsimp [rootGCD4]
  have h1 :
      Nat.gcd w.natAbs (Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs)) ∣
        Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs) :=
    Nat.gcd_dvd_right _ _
  have h2 : Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs) ∣
      Nat.gcd y.natAbs z.natAbs :=
    Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd y.natAbs z.natAbs ∣ z.natAbs :=
    Nat.gcd_dvd_right _ _
  exact h1.trans (h2.trans h3)

/-- Integer divisibility form for the first root. -/
theorem rootGCD4_dvd_w (w x y z : ℤ) :
    (rootGCD4 w x y z : ℤ) ∣ w := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_natAbs_w w x y z

/-- Integer divisibility form for the second root. -/
theorem rootGCD4_dvd_x (w x y z : ℤ) :
    (rootGCD4 w x y z : ℤ) ∣ x := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_natAbs_x w x y z

/-- Integer divisibility form for the third root. -/
theorem rootGCD4_dvd_y (w x y z : ℤ) :
    (rootGCD4 w x y z : ℤ) ∣ y := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_natAbs_y w x y z

/-- Integer divisibility form for the fourth root. -/
theorem rootGCD4_dvd_z (w x y z : ℤ) :
    (rootGCD4 w x y z : ℤ) ∣ z := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_natAbs_z w x y z

/-- A positive first square gap forces the root gcd to be positive. -/
theorem rootGCD4_pos_of_first_gap {w x y z Δ : ℤ}
    (hΔpos : 0 < Δ)
    (hxw : x ^ 2 - w ^ 2 = Δ) :
    0 < rootGCD4 w x y z := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hw0 : w = 0 := by
    rcases rootGCD4_dvd_w w x y z with ⟨k, hk⟩
    simpa [hzero] using hk
  have hx0 : x = 0 := by
    rcases rootGCD4_dvd_x w x y z with ⟨k, hk⟩
    simpa [hzero] using hk
  rw [hw0, hx0] at hxw
  norm_num at hxw
  nlinarith

/-- The square of the four-root gcd divides the first square gap. -/
theorem rootGCD4_sq_dvd_gap_xw (w x y z : ℤ) :
    ((rootGCD4 w x y z : ℤ) ^ 2) ∣ x ^ 2 - w ^ 2 := by
  rcases rootGCD4_dvd_x w x y z with ⟨qx, hx⟩
  rcases rootGCD4_dvd_w w x y z with ⟨qw, hw⟩
  refine ⟨qx ^ 2 - qw ^ 2, ?_⟩
  rw [hx, hw]
  ring

/-- If the first square gap is named `Δ`, then the gcd square divides `Δ`. -/
theorem rootGCD4_sq_dvd_delta_of_first_gap {w x y z Δ : ℤ}
    (hxw : x ^ 2 - w ^ 2 = Δ) :
    ((rootGCD4 w x y z : ℤ) ^ 2) ∣ Δ := by
  rw [← hxw]
  exact rootGCD4_sq_dvd_gap_xw w x y z

/--
If `g` is the positive four-root gcd and `w,x,y,z` are all `g` times
signed quotients, then the quotient tuple is primitive.
-/
theorem rootGCD4_eq_one_of_common_factor
    {w x y z p q r s : ℤ} {g : ℕ}
    (hgpos : 0 < g)
    (hgroot : g = rootGCD4 w x y z)
    (hw : w = (g : ℤ) * p)
    (hx : x = (g : ℤ) * q)
    (hy : y = (g : ℤ) * r)
    (hz : z = (g : ℤ) * s) :
    rootGCD4 p q r s = 1 := by
  let K : ℕ := rootGCD4 p q r s
  have hKp : K ∣ p.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_natAbs_w p q r s
  have hKq : K ∣ q.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_natAbs_x p q r s
  have hKr : K ∣ r.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_natAbs_y p q r s
  have hKs : K ∣ s.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_natAbs_z p q r s

  have hKg_w : K * g ∣ w.natAbs := by
    have hwa : w.natAbs = g * p.natAbs := by
      rw [hw, Int.natAbs_mul]
      simp
    rcases hKp with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hwa, ht]
    ring
  have hKg_x : K * g ∣ x.natAbs := by
    have hxa : x.natAbs = g * q.natAbs := by
      rw [hx, Int.natAbs_mul]
      simp
    rcases hKq with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hxa, ht]
    ring
  have hKg_y : K * g ∣ y.natAbs := by
    have hya : y.natAbs = g * r.natAbs := by
      rw [hy, Int.natAbs_mul]
      simp
    rcases hKr with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hya, ht]
    ring
  have hKg_z : K * g ∣ z.natAbs := by
    have hza : z.natAbs = g * s.natAbs := by
      rw [hz, Int.natAbs_mul]
      simp
    rcases hKs with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hza, ht]
    ring

  have hKg_root : K * g ∣ rootGCD4 w x y z := by
    dsimp [rootGCD4]
    exact Nat.dvd_gcd hKg_w (Nat.dvd_gcd hKg_x (Nat.dvd_gcd hKg_y hKg_z))
  have hKg_g : K * g ∣ g := by
    simpa [← hgroot] using hKg_root
  rcases hKg_g with ⟨t, ht⟩
  have hKt : 1 = K * t := by
    have hmul : g * 1 = g * (K * t) := by
      calc
        g * 1 = g := by ring
        _ = (K * g) * t := ht.symm
        _ = g * (K * t) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hmul
  have hK_dvd_one : K ∣ 1 := ⟨t, hKt.symm⟩
  have hK_one : K = 1 := Nat.dvd_one.mp hK_dvd_one
  simpa [K] using hK_one

/-- Full primitive division theorem for the four-square AP normalization layer. -/
theorem rootGCD4Division : RootGCD4Division := by
  intro w x y z Δ hΔpos hxw hyx hzy
  let gn : ℕ := rootGCD4 w x y z
  let g : ℤ := (gn : ℤ)
  let p : ℤ := w / g
  let q : ℤ := x / g
  let r : ℤ := y / g
  let s : ℤ := z / g
  let Δ' : ℤ := Δ / (g ^ 2)

  have hgnpos : 0 < gn := by
    dsimp [gn]
    exact rootGCD4_pos_of_first_gap hΔpos hxw
  have hgpos : 0 < g := by
    dsimp [g]
    exact_mod_cast hgnpos

  have hgw : g ∣ w := by
    simpa [g, gn] using rootGCD4_dvd_w w x y z
  have hgx : g ∣ x := by
    simpa [g, gn] using rootGCD4_dvd_x w x y z
  have hgy : g ∣ y := by
    simpa [g, gn] using rootGCD4_dvd_y w x y z
  have hgz : g ∣ z := by
    simpa [g, gn] using rootGCD4_dvd_z w x y z

  have hw : w = g * p := by
    dsimp [p]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgw).symm
  have hx : x = g * q := by
    dsimp [q]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgx).symm
  have hy : y = g * r := by
    dsimp [r]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgy).symm
  have hz : z = g * s := by
    dsimp [s]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgz).symm

  have hΔdvd : g ^ 2 ∣ Δ := by
    simpa [g, gn] using
      rootGCD4_sq_dvd_delta_of_first_gap (w := w) (x := x) (y := y) (z := z) hxw
  have hΔscale : Δ = g ^ 2 * Δ' := by
    dsimp [Δ']
    simpa [mul_comm] using (Int.ediv_mul_cancel hΔdvd).symm
  have hΔ'pos : 0 < Δ' := by
    have hprod : 0 < g ^ 2 * Δ' := by
      simpa [hΔscale] using hΔpos
    exact pos_of_mul_pos_left hprod (sq_nonneg g)

  have hpq : q ^ 2 - p ^ 2 = Δ' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hgpos))
    calc
      g ^ 2 * (q ^ 2 - p ^ 2) = (g * q) ^ 2 - (g * p) ^ 2 := by ring
      _ = x ^ 2 - w ^ 2 := by rw [← hx, ← hw]
      _ = Δ := hxw
      _ = g ^ 2 * Δ' := hΔscale
  have hrq : r ^ 2 - q ^ 2 = Δ' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hgpos))
    calc
      g ^ 2 * (r ^ 2 - q ^ 2) = (g * r) ^ 2 - (g * q) ^ 2 := by ring
      _ = y ^ 2 - x ^ 2 := by rw [← hy, ← hx]
      _ = Δ := hyx
      _ = g ^ 2 * Δ' := hΔscale
  have hsr : s ^ 2 - r ^ 2 = Δ' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hgpos))
    calc
      g ^ 2 * (s ^ 2 - r ^ 2) = (g * s) ^ 2 - (g * r) ^ 2 := by ring
      _ = z ^ 2 - y ^ 2 := by rw [← hz, ← hy]
      _ = Δ := hzy
      _ = g ^ 2 * Δ' := hΔscale

  have hprim : rootGCD4 p q r s = 1 := by
    exact rootGCD4_eq_one_of_common_factor
      (g := gn) (w := w) (x := x) (y := y) (z := z)
      (p := p) (q := q) (r := r) (s := s)
      hgnpos rfl
      (by simpa [g] using hw)
      (by simpa [g] using hx)
      (by simpa [g] using hy)
      (by simpa [g] using hz)

  exact ⟨g, p, q, r, s, Δ', hgpos, hΔ'pos,
    hw, hx, hy, hz, hpq, hrq, hsr, hprim⟩
```

If you paste this into the existing `N12FourSquaresAP.lean` after the definitions already present there, remove the repeated definitions at the top of the block and keep the helper theorems plus `rootGCD4Division`.

The route is deliberately independent of any N=12 elliptic-curve layer: it only uses `Nat.gcd`, `Int.natCast_dvd`, `Int.ediv_mul_cancel`, `Int.natAbs_mul`, and elementary ordered-ring arithmetic.
