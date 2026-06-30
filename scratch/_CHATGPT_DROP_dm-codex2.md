# Q2664 checked Eisenstein triple layer

Target file: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.

This is a self-contained checked layer: it imports only `Mathlib.Tactic`, defines the intended elementary predicates, and proves the five requested lemmas without `sorry`/axioms.  If the target file already has the definitions, omit the definition block and paste only the helper lemma plus theorem bodies.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Eisenstein norm equation in integer coordinates. -/
def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

/-- One of the two symmetric Eisenstein parametrizations. -/
def EisensteinParam (X Y Z m n : ℤ) : Prop :=
  Z = m ^ 2 - m * n + n ^ 2 ∧
    ((X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n - n ^ 2) ∨
      (Y = m ^ 2 - n ^ 2 ∧ X = 2 * m * n - n ^ 2))

/-- Parametrized triple, except for the unit exceptional triple. -/
def EisensteinTripleParamOrUnit (X Y Z : ℤ) : Prop :=
  (X = 1 ∧ Y = 1 ∧ Z = 1) ∨ ∃ m n : ℤ, EisensteinParam X Y Z m n

/-- A tiny integer helper avoiding any fragile `Int` unit API. -/
private lemma int_pos_eq_one_of_mul_eq_one {x y : ℤ}
    (hx : 0 < x) (hxy : x * y = 1) :
    x = 1 := by
  have hypos : 0 < y := by
    by_contra hy_not
    have hy_nonpos : y ≤ 0 := le_of_not_gt hy_not
    have hprod_nonpos : x * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx) hy_nonpos
    nlinarith [hxy, hprod_nonpos]
  have hxle : x ≤ 1 := by
    by_contra hx_not
    have hx_ge_two : (2 : ℤ) ≤ x := by omega
    have hy_ge_one : (1 : ℤ) ≤ y := by omega
    have hprod_ge_two : (2 : ℤ) ≤ x * y := by
      calc
        (2 : ℤ) = 2 * 1 := by ring
        _ ≤ x * y := by
          exact mul_le_mul hx_ge_two hy_ge_one (by norm_num) (by omega)
    nlinarith [hxy, hprod_ge_two]
  omega

/-- The parametrization identities satisfy the Eisenstein norm equation. -/
theorem eisensteinParam_triple {X Y Z m n : ℤ}
    (h : EisensteinParam X Y Z m n) :
    EisensteinTriple X Y Z := by
  rcases h with ⟨hZ, hcases⟩
  rcases hcases with hXY | hYX
  · rcases hXY with ⟨hX, hY⟩
    unfold EisensteinTriple
    rw [hZ, hX, hY]
    ring
  · rcases hYX with ⟨hY, hX⟩
    unfold EisensteinTriple
    rw [hZ, hX, hY]
    ring

/-- The Eisenstein norm equation is symmetric in `X` and `Y`. -/
theorem eisensteinTriple_symm {X Y Z : ℤ}
    (h : EisensteinTriple X Y Z) :
    EisensteinTriple Y X Z := by
  unfold EisensteinTriple at h ⊢
  rw [h]
  ring

/-- The parametrization predicate is symmetric in `X` and `Y`. -/
theorem eisensteinParam_symm {X Y Z m n : ℤ}
    (h : EisensteinParam X Y Z m n) :
    EisensteinParam Y X Z m n := by
  rcases h with ⟨hZ, hcases⟩
  refine ⟨hZ, ?_⟩
  rcases hcases with hXY | hYX
  · rcases hXY with ⟨hX, hY⟩
    exact Or.inr ⟨hX, hY⟩
  · rcases hYX with ⟨hY, hX⟩
    exact Or.inl ⟨hY, hX⟩

/-- If a positive primitive Eisenstein triple has `X = Y`, it is the unit triple. -/
theorem eisensteinTriple_unit_of_eq {X Y Z : ℤ}
    (hXpos : 0 < X) (hZpos : 0 < Z)
    (hcop : IsCoprime X Y)
    (htri : EisensteinTriple X Y Z)
    (hXY : X = Y) :
    X = 1 ∧ Y = 1 ∧ Z = 1 := by
  subst Y
  rcases hcop with ⟨r, s, hrs⟩
  have hXmul : X * (r + s) = 1 := by
    rw [← hrs]
    ring
  have hXone : X = 1 := int_pos_eq_one_of_mul_eq_one hXpos hXmul
  have hZpow : Z ^ 2 = 1 := by
    unfold EisensteinTriple at htri
    calc
      Z ^ 2 = X ^ 2 - X * X + X ^ 2 := htri
      _ = 1 := by
        rw [hXone]
        norm_num
  have hZmul : Z * Z = 1 := by
    simpa [pow_two] using hZpow
  have hZone : Z = 1 := int_pos_eq_one_of_mul_eq_one hZpos hZmul
  exact ⟨hXone, hXone, hZone⟩

/-- Factor identity with `P = 2*Z - (2*X-Y)` and `Q = 2*Z + (2*X-Y)`. -/
theorem eisensteinTriple_factor_identity {X Y Z : ℤ}
    (h : EisensteinTriple X Y Z) :
    (2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y)) = 3 * Y ^ 2 := by
  unfold EisensteinTriple at h
  calc
    (2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y))
        = 4 * Z ^ 2 - (2 * X - Y) ^ 2 := by ring
    _ = 3 * Y ^ 2 := by
      rw [h]
      ring

-- Useful API checks if you later prefer a gcd/unit-flavored proof of the unit case.
#check Int.isCoprime_iff_gcd_eq_one
#check isCoprime_self

end MazurProof.RationalPointsN12
```

Notes:

* The factor identity necessarily assumes `EisensteinTriple X Y Z`; otherwise `P*Q = 3*Y^2` is not true in general.
* `eisensteinTriple_unit_of_eq` destructs the `IsCoprime` witness directly.  After `X = Y`, Bezout gives `X * (r+s) = 1`; positivity forces `X = 1`, and then the triple equation plus `0 < Z` forces `Z = 1`.
* `Mathlib.Tactic` imports `Mathlib.Tactic.NormNum.IsCoprime`, which imports `Mathlib.RingTheory.Coprime.Lemmas`, so `IsCoprime`, `Int.isCoprime_iff_gcd_eq_one`, and `isCoprime_self` are available under this import at the current pin.
