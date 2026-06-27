import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic
import scratch.Bridge1HCD

/-!
# Bridge 1 (Even case): `preΨ'_root_Ψ₂Sq_ne'`

Proves that at a root `x` of `Ψ₂Sq`, `(W.preΨ' n).eval x ≠ 0` when `(n : K) ≠ 0`.

**Proof outline**:
1. **Eval lemma**: `(W.preΨ' n).eval x = preNormEDS' 0 C D n` at a Ψ₂Sq-root,
   where `C = W.Ψ₃.eval x` and `D = W.preΨ₄.eval x`, via `map_preNormEDS'`.
2. **Odd nonvanishing**: By `normEDSRec'`; at `b=0`, one summand vanishes per parity of m,
   leaving a product of odd-indexed terms that are nonzero by IH.
3. **Odd closed form**: `preNormEDS' 0 C D (2m+1) = oddSign m * C^(tri m)` by strong induction.
4. **Even closed forms** (mutual strong induction using hCD: `D² + 4C³ = 0`):
   - `preNormEDS' 0 C D (4k+2) = (2k+1 : K) * C^(2k(k+1))`
   - `preNormEDS' 0 C D (4(k+1)) = (k+1 : K) * D * C^(2k(k+2))`
5. **D ≠ 0** from hCD + C ≠ 0.
6. **Assembly**: closed form factors are nonzero since `(n : K) ≠ 0`, C ≠ 0, D ≠ 0.

Hard algebra closures in Section 4 are marked `sorry` — the structure is complete.
-/

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

open Polynomial

variable {K : Type*} [Field K]

/-! ### Section 1: Eval lemma -/

/-- At a `Ψ₂Sq`-root, `(preΨ' n).eval x = preNormEDS' 0 (Ψ₃.eval x) (preΨ₄.eval x) n`. -/
private lemma eval_preΨ'_at_Ψ₂Sq_root (W : WeierstrassCurve K) {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) (n : ℕ) :
    (W.preΨ' n).eval x = preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  -- W.preΨ' n = preNormEDS' (W.Ψ₂Sq^2) W.Ψ₃ W.preΨ₄ n in K[X]
  -- eval at x pushes through preNormEDS' via map_preNormEDS' applied to evalRingHom x
  rw [WeierstrassCurve.preΨ']
  -- Goal: (preNormEDS' (W.Ψ₂Sq^2) W.Ψ₃ W.preΨ₄ n).eval x = preNormEDS' 0 C D n
  -- Rewrite .eval x as application of (evalRingHom x)
  change (Polynomial.evalRingHom x) (preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n) =
    preNormEDS' 0 (W.Ψ₃.eval x) (W.preΨ₄.eval x) n
  rw [map_preNormEDS']
  simp [Polynomial.coe_evalRingHom, Polynomial.eval_pow, hs]

/-! ### Section 2: Odd nonvanishing -/

/-- When `b = 0` and `C ≠ 0`, all odd-indexed `preNormEDS' 0 C D N` are nonzero. -/
private theorem odd_ne_zero (C D : K) (hC : C ≠ 0) :
    ∀ N : ℕ, ¬Even N → preNormEDS' (0 : K) C D N ≠ 0 := by
  -- Use normEDSRec' with P n = (¬Even n → preNormEDS' 0 C D n ≠ 0)
  intro N
  induction N using normEDSRec' with
  | zero => intro hodd; exact absurd ⟨0, rfl⟩ hodd
  | one  => intro _; simp [preNormEDS'_one]
  | two  => intro hodd; exact absurd ⟨1, rfl⟩ hodd
  | three => intro _; simpa [preNormEDS'_three]
  | four => intro hodd; exact absurd ⟨2, rfl⟩ hodd
  | even m _ih => intro hodd; exact absurd ⟨m + 3, by omega⟩ hodd
  | odd m ih =>
    -- N = 2*(m+2)+1 = 2m+5, which is odd ✓
    intro hodd
    rw [preNormEDS'_odd]
    -- preNormEDS'_odd m : W(2(m+2)+1) = W(m+4)*W(m+2)^3*(if Even m then b else 1)
    --                                    - W(m+1)*W(m+3)^3*(if Even m then 1 else b)
    -- With b=0:
    by_cases hm : Even m
    · -- Even m: if-branches → 0 and 1
      simp only [hm, ↓reduceIte, mul_zero, zero_sub, mul_one]
      -- Goal: -(W(m+1) * W(m+3)^3) ≠ 0
      -- neg is injective (it's its own inverse), so -a = 0 ↔ a = 0
      intro heq
      -- heq : -(W * W^3) = 0, so W * W^3 = 0 by neg_injective
      have hmul_zero : preNormEDS' (0:K) C D (m+1) * preNormEDS' (0:K) C D (m+3)^3 = 0 :=
        neg_injective (heq.trans neg_zero.symm)
      exact absurd hmul_zero <| mul_ne_zero
          (ih (m+1) (by omega) (by obtain ⟨k, rfl⟩ := hm; exact fun ⟨j, hj⟩ => by omega))
          (pow_ne_zero _ (ih (m+3) (by omega)
              (by obtain ⟨k, rfl⟩ := hm; exact fun ⟨j, hj⟩ => by omega)))
    · -- Odd m: if-branches → 1 and 0
      simp only [hm, ↓reduceIte, mul_one, mul_zero, sub_zero]
      -- Remaining: W(m+4) * W(m+2)^3 ≠ 0
      apply mul_ne_zero
      · -- m+4 is odd since m is odd
        apply ih (m + 4) (by omega)
        rw [Nat.not_even_iff_odd] at hm; obtain ⟨k, rfl⟩ := hm
        exact fun ⟨j, hj⟩ => by omega
      · apply pow_ne_zero
        -- m+2 is odd since m is odd
        apply ih (m + 2) (by omega)
        rw [Nat.not_even_iff_odd] at hm; obtain ⟨k, rfl⟩ := hm
        exact fun ⟨j, hj⟩ => by omega

/-! ### Section 3: Odd closed form -/

/-- Triangular number: `tri m = 0 + 1 + ... + m`. -/
private def tri : ℕ → ℕ
  | 0 => 0
  | (m + 1) => tri m + (m + 1)

private lemma tri_zero : tri 0 = 0 := rfl
private lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := rfl

/-- Alternating sign ±1 with period 4, for the odd closed form. -/
private def oddSign : ℕ → K
  | 0 => 1
  | 1 => 1
  | (m + 2) => -(oddSign m)

@[simp] private lemma oddSign_zero : oddSign (K := K) 0 = 1 := rfl
@[simp] private lemma oddSign_one : oddSign (K := K) 1 = 1 := rfl
@[simp] private lemma oddSign_succ2 (m : ℕ) : oddSign (K := K) (m + 2) = -(oddSign m) := rfl

private lemma oddSign_ne_zero : ∀ m : ℕ, oddSign (K := K) m ≠ 0 := by
  intro m
  induction m using Nat.strongRecOn with | ind m ih => ?_
  match m with
  | 0 => simp
  | 1 => simp
  | m + 2 =>
    simp only [oddSign_succ2]
    -- Goal: -(oddSign m) ≠ 0
    intro heq
    exact ih m (by omega) (neg_injective (heq.trans neg_zero.symm))

/-- Odd closed form: `preNormEDS' 0 C D (2m+1) = oddSign m * C ^ tri m`. -/
private theorem odd_closed_form (C D : K) :
    ∀ m : ℕ, preNormEDS' (0 : K) C D (2 * m + 1) = oddSign (K := K) m * C ^ tri m := by
  intro m
  induction m using Nat.strongRecOn with | ind m ih => ?_
  match m with
  | 0 => simp [preNormEDS'_one, tri_zero]
  | 1 => simp [show 2 * 1 + 1 = 3 from rfl, preNormEDS'_three, tri_succ, tri_zero]
  | m + 2 =>
    -- Apply preNormEDS'_odd at parameter m (which covers index 2*(m+2)+1)
    have heq : 2 * (m + 2) + 1 = 2 * (m + 0 + 2) + 1 := by ring
    rw [heq, preNormEDS'_odd]
    by_cases hm : Even m
    · -- Even m: first summand has b=0
      -- simp before obtaining k so hm is still live
      simp only [hm, ↓reduceIte, mul_zero, zero_sub, mul_one]
      obtain ⟨k, rfl⟩ := hm
      -- m = k+k: W(k+k+1), W(k+k+3) in the goal
      -- Goal: -(W(k+k+1) * W(k+k+3)^3) = oddSign(k+k+2) * C^(tri(k+k+2))
      rw [show k + k + 1 = 2 * k + 1 from by omega]
      rw [show k + k + 3 = 2 * (k + 1) + 1 from by omega]
      -- IH: for j < 2k+2, use j=k and j=k+1
      rw [ih k (by omega), ih (k + 1) (by omega)]
      -- Now show: -(oddSign k * C^(tri k) * (oddSign(k+1) * C^(tri(k+1)))^3)
      --         = oddSign(2k+2) * C^(tri(2k+2))
      simp only [oddSign_succ2, tri_succ]
      -- After simp, both sides should match via ring (need C^a * C^b = C^(a+b))
      -- The exponent equality: tri k + 3*(tri k + (k+1)) = tri(2k) + (2k+1) + (2k+2)
      -- and oddSign(2k+2) = -(oddSign(2k)) via two applications of succ2
      -- These are tricky; use sorry for now and handle with pow_add + ring
      sorry
    · -- Odd m: second summand has b=0
      simp only [hm, ↓reduceIte, mul_zero, sub_zero, mul_one]
      obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hm
      -- m = 2*k+1: W(2*k+1+4) = W(2*(k+2)+1), W(2*k+1+2) = W(2*(k+1)+1) in goal
      rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 from by omega]
      rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 from by omega]
      -- IH: for j < 2k+3, use j=k+2 and j=k+1
      rw [ih (k + 2) (by omega), ih (k + 1) (by omega)]
      -- Show: oddSign(k+2) * C^(tri(k+2)) * (oddSign(k+1) * C^(tri(k+1)))^3
      --     = oddSign(2k+3) * C^(tri(2k+3))
      simp only [oddSign_succ2, tri_succ]
      sorry

/-! ### Section 4: D ≠ 0 at Ψ₂Sq-root -/

/-- `preΨ₄.eval x ≠ 0` when `Ψ₂Sq.eval x = 0` (from hCD + C ≠ 0 + 4 ≠ 0). -/
private lemma preΨ₄_eval_ne_zero (W : WeierstrassCurve K) {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) (h4 : (4 : K) ≠ 0) : W.preΨ₄.eval x ≠ 0 := by
  intro hD
  have hC := WeierstrassCurve.Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero W hs
  have hCD := WeierstrassCurve.preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root W hs
  rw [hD, zero_pow two_ne_zero, zero_add] at hCD
  -- Now: 4 * (Ψ₃.eval x)^3 = 0
  have hC3z : (W.Ψ₃.eval x) ^ 3 = 0 :=
    (mul_eq_zero.mp hCD).resolve_left h4
  exact hC (pow_eq_zero_iff three_ne_zero |>.mp hC3z)

/-! ### Section 5: Even closed forms -/

/-- Even closed forms for `preNormEDS' 0 C D`, proved by mutual strong induction.
    Key input: `hCD : D^2 + 4*C^3 = 0`.

    The two formulas are:
    - (A) `preNormEDS' 0 C D (4k+2) = (2k+1 : K) * C^(2k(k+1))`
    - (B) `preNormEDS' 0 C D (4(k+1)) = (k+1 : K) * D * C^(2k(k+2))`

    The algebra in each step uses `D^2 = -(4*C^3)` and `ring` after collecting C powers.
    Remaining algebra is `sorry`'d with the structure complete. -/
private theorem even_closed_forms {C D : K} (hC : C ≠ 0)
    (hCD : D ^ 2 + 4 * C ^ 3 = 0) :
    (∀ k : ℕ, preNormEDS' (0 : K) C D (4 * k + 2) =
        (2 * (k : K) + 1) * C ^ (2 * k * (k + 1))) ∧
    (∀ k : ℕ, preNormEDS' (0 : K) C D (4 * (k + 1)) =
        ((k : K) + 1) * D * C ^ (2 * k * (k + 2))) := by
  have hDsq : D ^ 2 = -(4 * C ^ 3) := by linear_combination hCD
  -- Simultaneous strong induction: prove A(k) ∧ B(k) for all k.
  -- B(k) may use A(k) (same level), so we prove A(k) first as a `have`, then use it for B(k).
  suffices h : ∀ k : ℕ,
      (preNormEDS' (0 : K) C D (4 * k + 2) = (2 * (k : K) + 1) * C ^ (2 * k * (k + 1))) ∧
      (preNormEDS' (0 : K) C D (4 * (k + 1)) = ((k : K) + 1) * D * C ^ (2 * k * (k + 2))) by
    exact ⟨fun k => (h k).1, fun k => (h k).2⟩
  intro k
  induction k using Nat.strongRecOn with | ind k ih => ?_
  -- ih : ∀ j < k, A(j) ∧ B(j)
  -- Helper: access A and B from ih
  have ihA : ∀ j < k, preNormEDS' (0:K) C D (4*j+2) = (2*(j:K)+1)*C^(2*j*(j+1)) :=
    fun j hj => (ih j hj).1
  have ihB : ∀ j < k, preNormEDS' (0:K) C D (4*(j+1)) = ((j:K)+1)*D*C^(2*j*(j+2)) :=
    fun j hj => (ih j hj).2
  -- Prove A(k) first
  have hA : preNormEDS' (0:K) C D (4*k+2) = (2*(k:K)+1)*C^(2*k*(k+1)) := by
    match k with
    | 0 => simp [preNormEDS'_two]
    | (k + 1) =>
      -- W₀(4(k+1)+2) = W₀(2*(2k+3)) via preNormEDS'_even at m=2k
      rw [show 4*(k+1)+2 = 2*(2*k+0+3) from by omega, preNormEDS'_even]
      rw [show 2*k+0+1 = 2*k+1 from by omega]
      rw [show 2*k+0+3 = 2*(k+1)+1 from by omega]
      rw [show 2*k+0+5 = 2*(k+2)+1 from by omega]
      rw [odd_closed_form C D k, odd_closed_form C D (k+1), odd_closed_form C D (k+2)]
      by_cases hk : Even k
      · obtain ⟨r, rfl⟩ := hk
        -- k = r+r: goal indices are 2*(r+r)+2, 2*(r+r)+4
        rw [show 2*(r+r)+2 = 4*r+2 from by omega]
        rw [show 2*(r+r)+4 = 4*(r+1) from by omega]
        rw [ihA r (by omega), ihB r (by omega)]
        sorry
      · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
        -- k = 2*r+1: goal indices are 2*(2*r+1)+2, 2*(2*r+1)+4
        rw [show 2*(2*r+1)+2 = 4*(r+1) from by omega]
        rw [show 2*(2*r+1)+4 = 4*(r+1)+2 from by omega]
        rw [ihB r (by omega), ihA (r+1) (by omega)]
        sorry
  -- Now prove B(k) using hA (formula A at k) and ih
  constructor
  · exact hA
  · -- Formula B at k: W₀(4(k+1)) = (k+1)*D*C^(2k(k+2))
    match k with
    | 0 => simp [preNormEDS'_four]
    | (k + 1) =>
      -- W₀(4(k+2)) = W₀(2*(2k+4)) via preNormEDS'_even at m=2k+1
      rw [show 4*(k+1+1) = 2*(2*k+1+3) from by omega, preNormEDS'_even]
      rw [show 2*k+1+2 = 2*(k+1)+1 from by omega]
      rw [show 2*k+1+4 = 2*(k+2)+1 from by omega]
      rw [odd_closed_form C D (k+1), odd_closed_form C D (k+2)]
      rw [show 2*k+1+1 = 2*k+2 from by omega]
      rw [show 2*k+1+3 = 2*k+4 from by omega]
      rw [show 2*k+1+5 = 2*k+6 from by omega]
      by_cases hk : Even k
      · obtain ⟨r, rfl⟩ := hk
        -- k=2r: W(2k+2)=W(4r+2)=A(r), W(2k+4)=W(4(r+1))=B(r), W(2k+6)=W(4(r+1)+2)=A(r+1)
        -- Note: A(r+1) = A(k+1) when k=2r, so outer k+1 → inner k = 2r, r+1 = (k+1)/2+1 < k+2
        -- But actually A at r+1: when k = 2r, outer k+1 in formula B = 2r+1, and r+1 < 2r+1 for r≥1
        -- For r=0: A at r+1=1 = A(1) which is hA in the outer induction at k=1 — NOT available!
        -- Instead, use hA from the current outer k = 2r+1+1 = 2r+2:
        --   outer k (in strongRecOn) = k+1+1 (the Nat.strongRecOn k), here k+1 is inner
        -- Actually: the outer `k` in strongRecOn is the `k` passed to the intro, which is
        -- the outer k+1 in the `match k with | k+1 => ...`. So inner k = outer k - 1 = 2r.
        -- hA says A(outer k) = A(k+1) where outer k = 2r+1. So A at 2r+1 is hA!
        -- But we need A at inner k+1 = 2r+1 = outer k — YES, that's hA!
        -- k=r+r: goal indices 2*(r+r)+2, 2*(r+r)+4, 2*(r+r)+6
        rw [show 2*(r+r)+2 = 4*r+2 from by omega]
        rw [show 2*(r+r)+4 = 4*(r+1) from by omega]
        rw [show 2*(r+r)+6 = 4*(r+1)+2 from by omega]
        rw [ihA r (by omega), ihB r (by omega)]
        -- A(r+1): type matches ihA's output (using ↑(r+1) and r+1+1 forms)
        have hAr1 : preNormEDS' (0:K) C D (4*(r+1)+2) =
            (2*(↑(r+1))+1)*C^(2*(r+1)*(r+1+1)) := by
          rcases Nat.eq_zero_or_pos r with rfl | hr
          · simpa using hA
          · exact ihA (r+1) (by omega)
        rw [hAr1]
        sorry
      · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
        -- k=2*r+1: goal indices 2*(2*r+1)+2, 2*(2*r+1)+4, 2*(2*r+1)+6
        rw [show 2*(2*r+1)+2 = 4*(r+1) from by omega]
        rw [show 2*(2*r+1)+4 = 4*(r+1)+2 from by omega]
        rw [show 2*(2*r+1)+6 = 4*(r+2) from by omega]
        rw [ihB r (by omega), ihA (r+1) (by omega), ihB (r+1) (by omega)]
        sorry

/-! ### Section 6: Main theorem -/

namespace WeierstrassCurve

/-- At a root `x` of `Ψ₂Sq`, `(preΨ' n).eval x ≠ 0` whenever `(n : K) ≠ 0`. -/
theorem preΨ'_root_Ψ₂Sq_ne' (W : WeierstrassCurve K) {n : ℕ} (hn : (n : K) ≠ 0)
    {x : K} (hs : W.Ψ₂Sq.eval x = 0) : (W.preΨ' n).eval x ≠ 0 := by
  rw [eval_preΨ'_at_Ψ₂Sq_root W hs n]
  -- Set C = Ψ₃(x), D = preΨ₄(x)
  set C := W.Ψ₃.eval x with hC_def
  set D := W.preΨ₄.eval x with hD_def
  have hC : C ≠ 0 := WeierstrassCurve.Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero W hs
  have hCD : D ^ 2 + 4 * C ^ 3 = 0 :=
    WeierstrassCurve.preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root W hs
  -- Case: n odd
  rcases Nat.even_or_odd n with hne | hno
  swap
  · exact odd_ne_zero C D hC n (Nat.not_even_iff_odd.mpr hno)
  -- Case: n even
  · -- (n : K) ≠ 0 and n even → 2 ≠ 0 in K
    have h2 : (2 : K) ≠ 0 := by
      intro h2; apply hn
      obtain ⟨m', hm'⟩ := hne
      -- n = m' + m' = 2 * m'
      have : (n : K) = 2 * (m' : K) := by push_cast [hm']; ring
      rw [this, h2, zero_mul]
    have h4 : (4 : K) ≠ 0 := by
      intro h4; apply h2
      have h22 : (2 : K) * 2 = 4 := by norm_num
      have : (2 : K) * 2 = 0 := by rw [h22]; exact h4
      exact (mul_eq_zero.mp this).elim id id
    have hD : D ≠ 0 := preΨ₄_eval_ne_zero W hs h4
    obtain ⟨hfA, hfB⟩ := even_closed_forms hC hCD
    -- n is even: write n = 2 * m' for some m'
    obtain ⟨m', hm'⟩ := hne
    -- hm' : n = m' + m', which is 2 * m' (but use omega to avoid + vs * mismatch)
    -- Split on parity of m'
    rcases Nat.even_or_odd m' with ⟨r, hr⟩ | ⟨r, hr⟩
    · -- m' = r + r, n = 4r
      -- Check r ≠ 0 (else n = 0 contradicts hn)
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · -- n = 0 (r=0 → m'=0 → n=0)
        exfalso; apply hn
        have : n = 0 := by omega
        simp [this]
      · -- r ≥ 1, write r = s+1
        obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr_pos.ne'
        -- n = 4*(s+1): use hfB at s
        have hn_eq : n = 4 * (s + 1) := by omega
        rw [hn_eq, hfB s]
        -- = (s+1 : K) * D * C^(...)
        apply mul_ne_zero (mul_ne_zero _ hD) (pow_ne_zero _ hC)
        -- (s+1 : K) ≠ 0
        intro hs1
        apply hn
        rw [hn_eq]; push_cast
        linear_combination (4 : K) * hs1
    · -- m' = 2*r+1, n = 4r+2
      have hn_eq : n = 4 * r + 2 := by omega
      rw [hn_eq, hfA r]
      -- = (2r+1 : K) * C^(...)
      apply mul_ne_zero _ (pow_ne_zero _ hC)
      -- (2r+1 : K) ≠ 0
      intro hr1
      apply hn
      rw [hn_eq]; push_cast
      linear_combination (2 : K) * hr1

end WeierstrassCurve
