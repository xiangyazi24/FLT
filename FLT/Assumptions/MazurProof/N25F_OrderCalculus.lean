import FLT.Assumptions.MazurProof.N25F_SharpBasis
import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalAddition
import FLT.Assumptions.MazurProof.N25F_ProjectiveProductFormula
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree
import FLT.Assumptions.MazurProof.N25F_NoQuadraticPoints
import FLT.Assumptions.MazurProof.N25F_XChartFractionInjective

/-!
# A calculus of orders at the closed points of the N25 curve

For a closed point `A` of the full projective grading and a function `f` on the
genus-four N25 quotient curve over `F₂`, `ordAt A f` is the coefficient at `A`
of the actual projective principal divisor of `f` (and `0` for `f = 0`).
`Ge A f k` says `f = 0` or `ord_A f ≥ k`.

The order is additive on products and ultrametric on sums, and these two rules
yield a small calculus (`Ge.add`, `Ge.mul`, `Ge.cancel`, `ordAt_add_of_lt`).
Together with the known local data at the five rational points

* `X = [1:0:0:0]`, `YZ = [0:1:1:0]`, `Z = [0:0:1:0]` on the boundary `w = 0`,
* `R = [0:0:0:1]` and `P = [1:1:0:1]` on the affine chart `w = 1`,

it determines divisors of explicit functions.  The closing lemma
`principal_eq_of_le` turns lower bounds into equalities: a degree-zero divisor
bounded above by the principal divisor of `f` is that principal divisor.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_OrderCalculus
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_PrincipalOrderAddition
open N25F_ProjectivePrincipalAddition N25F_ProjectiveProductFormula
open N25F_NonBoundaryPrincipalDivisor N25F_NoQuadraticPoints N25F_ProjectiveDivisorDegree
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap N25F_ZChartWChartEquiv
open N25F_SharpBasis N25F_XChartFractionInjective N25F_XChartFractionMap
open RationalPointsN25QuotientTwoAffineCharts
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local notation "F" => algebraMap N25F_NonBoundaryPrincipalDivisor.W K

/-- The order of a function at a full closed point: the coefficient of its
projective principal divisor, with the junk value `0` at `f = 0`. -/
def ordAt (A : fullClosedPointGrading25Two.Atom) (f : K) : ℤ :=
  haveI := Classical.dec (f = 0)
  if h : f = 0 then 0 else projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f h)) A

/-- `f` vanishes to order at least `k` at `A` (vacuous for `f = 0`). -/
def Ge (A : fullClosedPointGrading25Two.Atom) (f : K) (k : ℤ) : Prop :=
  f = 0 ∨ k ≤ ordAt A f

variable (A : fullClosedPointGrading25Two.Atom)

theorem ordAt_of_ne {f : K} (h : f ≠ 0) :
    ordAt A f = projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f h)) A := by
  unfold ordAt
  exact dif_neg h

/-! ## Products and sums -/

theorem ordAt_mul {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordAt A (f * g) = ordAt A f + ordAt A g := by
  rw [ordAt_of_ne A (mul_ne_zero hf hg), ordAt_of_ne A hf, ordAt_of_ne A hg]
  have : Additive.ofMul (Units.mk0 (f * g) (mul_ne_zero hf hg)) =
      Additive.ofMul (Units.mk0 f hf) + Additive.ofMul (Units.mk0 g hg) := by
    rw [← ofMul_mul]
    congr 1
    ext
    simp
  rw [this, map_add, Finsupp.add_apply]

theorem ordAt_one : ordAt A 1 = 0 := by
  have h := ordAt_mul A (one_ne_zero (α := K)) one_ne_zero
  rw [one_mul] at h
  omega

theorem ordAt_neg_one : ordAt A (-1) = 0 := by
  have h := ordAt_mul A (neg_ne_zero.mpr (one_ne_zero (α := K)))
    (neg_ne_zero.mpr (one_ne_zero (α := K)))
  rw [neg_mul_neg, one_mul, ordAt_one] at h
  omega

theorem ordAt_neg (f : K) : ordAt A (-f) = ordAt A f := by
  by_cases hf : f = 0
  · rw [hf, neg_zero]
  rw [neg_eq_neg_one_mul, ordAt_mul A (neg_ne_zero.mpr one_ne_zero) hf, ordAt_neg_one,
    zero_add]

theorem ordAt_inv {f : K} (hf : f ≠ 0) : ordAt A f⁻¹ = -ordAt A f := by
  have h := ordAt_mul A hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ordAt_one] at h
  omega

theorem ordAt_add_ge {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0) :
    min (ordAt A f) (ordAt A g) ≤ ordAt A (f + g) := by
  rw [ordAt_of_ne A hf, ordAt_of_ne A hg, ordAt_of_ne A hs]
  exact projectivePrincipalDivisor_add_ge_min _ _ _ (by simp) A

/-! ## The predicate `Ge` -/

theorem ge_zero (k : ℤ) : Ge A 0 k := Or.inl rfl

theorem ge_of_eq {f : K} {k : ℤ} (h : ordAt A f = k) : Ge A f k := Or.inr h.ge

theorem ge_one_zero : Ge A 1 0 := ge_of_eq A (ordAt_one A)

theorem Ge.le {f : K} {k : ℤ} (h : Ge A f k) (hf : f ≠ 0) : k ≤ ordAt A f :=
  h.resolve_left hf

theorem Ge.mono {f : K} {k k' : ℤ} (h : Ge A f k) (hk : k' ≤ k) : Ge A f k' :=
  h.imp_right fun h => hk.trans h

theorem Ge.add {f g : K} {k : ℤ} (hf : Ge A f k) (hg : Ge A g k) : Ge A (f + g) k := by
  by_cases hs : f + g = 0
  · exact Or.inl hs
  right
  rcases hf with rfl | hf
  · simpa using hg.resolve_left (by simpa using hs)
  rcases hg with rfl | hg
  · simpa using hf
  by_cases hf0 : f = 0
  · subst hf0; simpa using hg
  by_cases hg0 : g = 0
  · subst hg0; simpa using hf
  exact (le_min hf hg).trans (ordAt_add_ge A hf0 hg0 hs)

theorem Ge.neg {f : K} {k : ℤ} (h : Ge A f k) : Ge A (-f) k := by
  rcases h with rfl | h
  · exact Or.inl neg_zero
  · exact Or.inr (by rwa [ordAt_neg])

theorem Ge.sub {f g : K} {k : ℤ} (hf : Ge A f k) (hg : Ge A g k) : Ge A (f - g) k := by
  rw [sub_eq_add_neg]
  exact hf.add A hg.neg

theorem Ge.mul {f g : K} {a b : ℤ} (hf : Ge A f a) (hg : Ge A g b) : Ge A (f * g) (a + b) := by
  rcases hf with rfl | hf
  · exact Or.inl (zero_mul g)
  rcases hg with rfl | hg
  · exact Or.inl (mul_zero f)
  by_cases hf0 : f = 0
  · exact Or.inl (by rw [hf0, zero_mul])
  by_cases hg0 : g = 0
  · exact Or.inl (by rw [hg0, mul_zero])
  right
  rw [ordAt_mul A hf0 hg0]
  omega

theorem Ge.pow {f : K} {a : ℤ} (hf : Ge A f a) (n : ℕ) : Ge A (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using ge_one_zero A
  | succ n ih =>
      rw [pow_succ]
      exact (ih.mul A hf).mono A (by push_cast; linarith)

/-- Cancel a nonzero factor of known order. -/
theorem Ge.cancel {f u : K} {k : ℤ} (h : Ge A (f * u) k) (hu : u ≠ 0) :
    Ge A f (k - ordAt A u) := by
  rcases h with h | h
  · exact Or.inl ((mul_eq_zero.mp h).resolve_right hu)
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  rw [ordAt_mul A hf hu] at h
  omega

theorem Ge.of_eq {f g : K} {k : ℤ} (h : Ge A f k) (hfg : f = g) : Ge A g k := hfg ▸ h

/-- In a sum, a strictly smaller order wins. -/
theorem ordAt_add_of_lt {f g : K} {a : ℤ} (hf : f ≠ 0) (hfa : ordAt A f = a)
    (hg : Ge A g (a + 1)) : f + g ≠ 0 ∧ ordAt A (f + g) = a := by
  have hfge : Ge A f a := ge_of_eq A hfa
  have hsum : Ge A (f + g) a := hfge.add A (hg.mono A (by omega))
  have hne : f + g ≠ 0 := by
    intro h0
    have hfg : f = -g := eq_neg_of_add_eq_zero_left h0
    have := (hg.neg A).le A (by rw [← hfg]; exact hf)
    rw [← hfg] at this
    omega
  refine ⟨hne, le_antisymm ?_ (hsum.le A hne)⟩
  by_contra hlt
  push Not at hlt
  have h2 : Ge A (f + g - g) (a + 1) := Ge.sub A (Or.inr (by omega)) hg
  rw [add_sub_cancel_right] at h2
  have := h2.le A hf
  omega

/-- `1 + m` is a unit at `A` when `m` vanishes there. -/
theorem ordAt_one_add {m : K} (hm : Ge A m 1) : 1 + m ≠ 0 ∧ ordAt A (1 + m) = 0 :=
  ordAt_add_of_lt A one_ne_zero (ordAt_one A) (by simpa using hm)

/-- A function and its order: if `f ≠ 0` with `Ge f k` exact, then `Ge` of its
inverse. -/
theorem ge_inv_of_eq {f : K} {a : ℤ} (hf : f ≠ 0) (hfa : ordAt A f = a) : Ge A f⁻¹ (-a) :=
  ge_of_eq A (by rw [ordAt_inv A hf, hfa])

/-! ## Closing a degree-zero divisor -/

/-- If `D` has degree zero and `D ≤ div f` pointwise, then `D = div f`. -/
theorem principal_eq_of_le (f : K) (hf : f ≠ 0) (D : ProjectiveDivisor25Two)
    (hD : fullClosedPointGrading25Two.divisorDegree D = 0)
    (hle : ∀ B, Ge B f (D B)) :
    projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf)) = D := by
  set E := projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf)) - D with hE
  have hEnn : ∀ B, 0 ≤ E B := by
    intro B
    have h := (hle B).le B hf
    rw [ordAt_of_ne B hf] at h
    simp only [hE, Finsupp.coe_sub, Pi.sub_apply]
    omega
  have hdeg : fullClosedPointGrading25Two.divisorDegree E = 0 := by
    rw [hE, map_sub, projectivePrincipalDivisor_degree_eq_zero, hD, sub_zero]
  have hE0 : E = 0 := by
    ext B
    have h := le_divisorDegree_of_nonneg E hEnn B
    have hpos := fullClosedPointGrading25Two.atomDegree_pos B
    have := hEnn B
    rw [hdeg] at h
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    nlinarith
  exact sub_eq_zero.mp hE0

end MazurProof.N25F_OrderCalculus
