module

public import Mathlib.Algebra.DualNumber

/-! # SEAM1 / E1 — dual-number jet scaffolding (notation + tangent-at-O)

The verifiable scaffolding for the rootwise tangent core: the `D K` dual-number notation and the
`TangentO` first-order chart at `O`, whose `n`-fold sum is scalar `n` (the `d[n]|_O = n·id` fact at
the tangent-coordinate level). The deep raw-coordinate bridge is isolated separately. -/

open scoped DualNumber

namespace WeierstrassCurve.SEAM1

variable {K : Type*} [Field K]

abbrev D (K : Type*) [Field K] := DualNumber K

namespace Dual
abbrev c (x : K) : D K := TrivSqZeroExt.inl x
abbrev e (v : K) : D K := TrivSqZeroExt.inr v
@[simp] lemma fst_c (x : K) : TrivSqZeroExt.fst (c x : D K) = x := rfl
@[simp] lemma snd_c (x : K) : TrivSqZeroExt.snd (c x : D K) = 0 := rfl
@[simp] lemma fst_e (v : K) : TrivSqZeroExt.fst (e v : D K) = 0 := rfl
@[simp] lemma snd_e (v : K) : TrivSqZeroExt.snd (e v : D K) = v := rfl
end Dual

namespace TangentO

/-- First-order `n`-fold sum in the tangent coordinate at `O`. -/
def nsmul₁ : ℕ → K → K
  | 0, _ => 0
  | n + 1, u => nsmul₁ n u + u

@[simp] lemma nsmul₁_zero (u : K) : nsmul₁ 0 u = 0 := rfl
@[simp] lemma nsmul₁_succ (n : ℕ) (u : K) : nsmul₁ (n + 1) u = nsmul₁ n u + u := rfl

/-- The first-order tangent of `[n]` at `O` is scalar multiplication by `(n : K)`. -/
lemma nsmul₁_eq_natCast_mul (n : ℕ) (u : K) : nsmul₁ n u = (n : K) * u := by
  induction n with
  | zero => simp
  | succ n ih => rw [nsmul₁_succ, ih, Nat.cast_succ, add_mul, one_mul]

end TangentO

end WeierstrassCurve.SEAM1
