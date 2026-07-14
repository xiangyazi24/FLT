import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18AddCongr
import FLT.Assumptions.MazurProof.N18GoodModelValCoords
import FLT.Assumptions.MazurProof.N18VpiWrapper
import scratch.KeystoneEDS

/-!
# Package II for the N18 formal kernel

This file proves that the second step of the `pi`-adic formal filtration of
the good model `E0Good` is torsion-free.  The proof uses the projective
division-polynomial coordinates of scalar multiples.  At a point with
`ordPi x = -2r`, the leading terms of `Phi_n(x)` and `PsiSq_n(x)` strictly
dominate all lower terms.  For `3 ∤ n` this preserves `r`; for `n = 3` and
`r >= 2`, the extra orders of the first two coefficients give `r + 3`.
-/

open scoped Classical NumberField WeierstrassCurve.Affine

namespace MazurProof.N18PackageII

open Polynomial
open MazurProof.N18RouteC
open MazurProof.N18RouteC.FieldArithmetic
open MazurProof.N18RouteC.GoodModel
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

/-- Formal parameter `z = -x/y` on the good model, totalized by `z(O) = 0`. -/
def zParamGood : E0GoodPoint → L
  | .zero => 0
  | .some x y _ => -x / y

@[simp] theorem zParamGood_zero : zParamGood (0 : E0GoodPoint) = 0 := rfl

@[simp] theorem zParamGood_some (x y : L)
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y) :
    zParamGood (.some x y h) = -x / y := rfl

/-- The pointwise formal-kernel predicate on the good model. -/
def InFormalKernel : E0GoodPoint → Prop
  | .zero => True
  | .some x _ _ => ordPi x < 0

@[simp] theorem zero_mem_formalKernel : InFormalKernel (0 : E0GoodPoint) := trivial

/-! ## The first two nonlinear coefficients of `[3]` -/

/-- Quadratic coefficient of the good-model tripling series. -/
def c₂ : L := -3 * E0Good.a₁

/-- Cubic coefficient of the good-model tripling series. -/
def c₃ : L := E0Good.a₁ ^ 2 - 8 * E0Good.a₂

private theorem pi_ne_zero : pi ≠ 0 := by
  intro h
  have hp := ordPi_pi
  rw [h, ordPi_zero] at hp
  omega

private theorem ordPi_nonneg_of_ringOfIntegers (u : OL) :
    0 ≤ ordPi (u : L) := by
  rcases eq_or_ne (u : L) 0 with h0 | hne
  · rw [h0, ordPi_zero]
  · have hle : v3 (u : L) ≤ 1 := by
      show p3.valuation L (u : L) ≤ 1
      simpa using
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one
          (K := L) p3 u)
    have hlog : WithZero.log (v3 (u : L)) ≤ 0 := by
      have h := (WithZero.log_le_log (v3_ne_zero hne) one_ne_zero).mpr hle
      rwa [WithZero.log_one] at h
    unfold ordPi
    linarith

theorem c₂_eq : c₂ = -3 * (a ^ 2 - 2) := by
  simp [c₂, E0Good]

theorem c₃_eq : c₃ = 7 * a ^ 2 - 15 * a - 4 := by
  simp only [c₃, E0Good]
  ring_nf
  rw [a_pow_four]
  ring

private theorem ordPi_pow {x : L} (hx : x ≠ 0) (n : ℕ) :
    ordPi (x ^ n) = (n : ℤ) * ordPi x := by
  induction n with
  | zero => simp [ordPi_one]
  | succ n ih =>
      rw [pow_succ, ordPi_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

private theorem ordPi_a₁_good : ordPi E0Good.a₁ = 0 := by
  have hmul : E0Good.a₁ * (a ^ 2 - a - 1) = 1 := by
    simp only [E0Good]
    ring_nf
    rw [a_pow_four, a_cubic]
    ring
  have ha₁ : E0Good.a₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  have hinv : a ^ 2 - a - 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact zero_ne_one hmul
  have haInt : IsIntegral ℤ a := (pi_isIntegral.add isIntegral_one)
  let a₁Int : OL := aInteger ^ 2 - 2
  have ha₁map : (a₁Int : L) = E0Good.a₁ := by
    simp [a₁Int, aInteger, E0Good]
    exact map_natCast (algebraMap OL L) 2
  have hinvInt : IsIntegral ℤ (a ^ 2 - a - 1) :=
    ((haInt.pow 2).sub haInt).sub (isIntegral_intCast 1)
  have hv := congrArg ordPi hmul
  rw [ordPi_mul ha₁ hinv, ordPi_one] at hv
  have hnonneg₁ : 0 ≤ ordPi E0Good.a₁ := by
    rw [← ha₁map]
    exact ordPi_nonneg_of_ringOfIntegers a₁Int
  have hnonnegInv : 0 ≤ ordPi (a ^ 2 - a - 1) := by
    simpa using ordPi_nonneg_of_ringOfIntegers
      (⟨a ^ 2 - a - 1, hinvInt⟩ : OL)
  omega

/-- The quadratic coefficient has exact `pi`-order three. -/
theorem ordPi_c₂ : ordPi c₂ = 3 := by
  have ha₁ : E0Good.a₁ ≠ 0 := by
    intro h
    have hmul : E0Good.a₁ * (a ^ 2 - a - 1) = 1 := by
      simp only [E0Good]
      ring_nf
      rw [a_pow_four, a_cubic]
      ring
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  rw [c₂, ordPi_mul (by norm_num) ha₁, ordPi_neg, ordPi_three,
    ordPi_a₁_good]
  norm_num

private theorem c₃_pi_expansion : c₃ = -pi + (-12 + 7 * pi ^ 2) := by
  rw [c₃_eq]
  change 7 * (pi + 1) ^ 2 - 15 * (pi + 1) - 4 =
    -pi + (-12 + 7 * pi ^ 2)
  ring

/-- The cubic coefficient has exact `pi`-order one. -/
theorem ordPi_c₃ : ordPi c₃ = 1 := by
  let q : L := 7 - 4 * pi * (pi ^ 2 + 3 * pi + 1)
  have htail : (-12 : L) + 7 * pi ^ 2 = pi ^ 2 * q := by
    dsimp [q]
    rw [show (-12 : L) + 7 * pi ^ 2 =
      -4 * 3 + 7 * pi ^ 2 by ring]
    nth_rewrite 1 [three_eq_pi_cubed_mul_inverse]
    ring
  let qInt : OL :=
    7 - 4 * piInteger * (piInteger ^ 2 + 3 * piInteger + 1)
  have hqMap : (qInt : L) = q := by
    simp [qInt, q, piInteger]
    rw [map_ofNat (algebraMap OL L) 7,
      map_ofNat (algebraMap OL L) 4,
      map_ofNat (algebraMap OL L) 3]
  rw [c₃_pi_expansion, htail]
  by_cases hq : q = 0
  · simp [hq, ordPi_pi]
  · have htail0 : pi ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero 2 pi_ne_zero) hq
    have htailOrd : 2 ≤ ordPi (pi ^ 2 * q) := by
      rw [ordPi_mul (pow_ne_zero 2 pi_ne_zero) hq,
        ordPi_pow pi_ne_zero, ordPi_pi]
      have hqNonneg : 0 ≤ ordPi q := by
        rw [← hqMap]
        exact ordPi_nonneg_of_ringOfIntegers qInt
      omega
    rw [ordPi_add_eq_of_lt (neg_ne_zero.mpr pi_ne_zero) htail0]
    · simp [ordPi_pi]
    · simp only [ordPi_neg, ordPi_pi]
      omega

/-! ## Integral division polynomials and leading-term valuation -/

/-- The integral good model whose scalar extension to `L` is `E0Good`. -/
def E0GoodInt : WeierstrassCurve OL where
  a₁ := aInteger ^ 2 - 2
  a₂ := -aInteger ^ 2 + 2 * aInteger + 1
  a₃ := aInteger + 1
  a₄ := -aInteger ^ 2 + 1
  a₆ := 4 * aInteger ^ 2 - 7 * aInteger - 3

theorem E0GoodInt_map :
    E0GoodInt.map (algebraMap OL L) = E0Good := by
  have hmapNat (n : ℕ) : algebraMap OL L (n : OL) = (n : L) :=
    map_natCast (algebraMap OL L) n
  ext
  · simp [E0GoodInt, E0Good, aInteger]
    exact hmapNat 2
  · simp [E0GoodInt, E0Good, aInteger]
    left
    exact hmapNat 2
  · simp [E0GoodInt, E0Good, aInteger]
  · simp [E0GoodInt, E0Good, aInteger]
  · simp [E0GoodInt, E0Good, aInteger]
    rw [map_ofNat (algebraMap OL L) 4,
      map_ofNat (algebraMap OL L) 7,
      map_ofNat (algebraMap OL L) 3]

private theorem ordPi_finset_sum_gt_or_zero {ι : Type*} {q : L} {s : Finset ι} {f : ι → L}
    (hgt : ∀ i ∈ s, f i ≠ 0 → ordPi q < ordPi (f i)) :
    (∑ i ∈ s, f i) = 0 ∨ ordPi q < ordPi (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hs : ∀ j ∈ s, f j ≠ 0 → ordPi q < ordPi (f j) := by
        intro j hj
        exact hgt j (Finset.mem_insert_of_mem hj)
      rcases ih hs with hsum | hsum
      · by_cases hfi : f i = 0
        · left
          simp [Finset.sum_insert hi, hfi, hsum]
        · right
          simpa [Finset.sum_insert hi, hsum] using hgt i (by simp) hfi
      · by_cases hfi : f i = 0
        · right
          simpa [Finset.sum_insert hi, hfi] using hsum
        · by_cases htail : ∑ j ∈ s, f j = 0
          · right
            simpa [Finset.sum_insert hi, htail] using hgt i (by simp) hfi
          · by_cases hall : f i + ∑ j ∈ s, f j = 0
            · left
              simpa [Finset.sum_insert hi] using hall
            · right
              rw [Finset.sum_insert hi]
              exact lt_of_lt_of_le
                (lt_min (hgt i (by simp) hfi) hsum)
                (ordPi_add_ge hfi htail hall)

/-- Evaluation of an integral polynomial at an element of negative order is
controlled by its leading term when the leading coefficient is a unit. -/
private theorem ordPi_eval₂_eq_natDegree_mul
    (p : OL[X]) (hp : p ≠ 0) {x : L} (hx : ordPi x < 0)
    (hlc : ordPi ((p.leadingCoeff : OL) : L) = 0) :
    ordPi (p.eval₂ (algebraMap OL L) x) = (p.natDegree : ℤ) * ordPi x := by
  classical
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hx
    omega
  let d := p.natDegree
  let lead : L := (p.leadingCoeff : L) * x ^ d
  let tail : L := ∑ i ∈ Finset.range d, (p.coeff i : L) * x ^ i
  have hlc0 : (p.leadingCoeff : L) ≠ 0 := by
    have hlcOL : p.leadingCoeff ≠ 0 := p.leadingCoeff_ne_zero.mpr hp
    intro h
    apply hlcOL
    exact_mod_cast h
  have hlead0 : lead ≠ 0 := mul_ne_zero hlc0 (pow_ne_zero d hx0)
  have hleadOrd : ordPi lead = (d : ℤ) * ordPi x := by
    rw [ordPi_mul hlc0 (pow_ne_zero d hx0), ordPi_pow hx0, hlc]
    omega
  have hshape : p.eval₂ (algebraMap OL L) x = tail + lead := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
    dsimp [tail, lead, d]
  have htail : tail = 0 ∨ ordPi lead < ordPi tail := by
    dsimp only [tail]
    apply ordPi_finset_sum_gt_or_zero
    intro i hi hterm
    have hid : i < d := Finset.mem_range.mp hi
    have hci : (p.coeff i : L) ≠ 0 := by
      intro h
      apply hterm
      rw [h, zero_mul]
    have hpow : x ^ i ≠ 0 := pow_ne_zero i hx0
    rw [ordPi_mul hci hpow, ordPi_pow hx0, hleadOrd]
    have hcoeff : 0 ≤ ordPi ((p.coeff i : OL) : L) :=
      ordPi_nonneg_of_ringOfIntegers (p.coeff i)
    have hidz : (i : ℤ) < d := by exact_mod_cast hid
    nlinarith
  rw [hshape]
  rcases htail with htail | htail
  · simp only [htail, zero_add, hleadOrd, d]
  · by_cases htail0 : tail = 0
    · simp only [htail0, zero_add, hleadOrd, d]
    · rw [add_comm, ordPi_add_eq_of_lt hlead0 htail0 htail, hleadOrd]

private theorem psi_ne_zero_charZero (W : WeierstrassCurve L) [W.IsElliptic] :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hpsi₂ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
          (Polynomial.C_ne_zero.mpr (two_ne_zero (α := L))),
        Polynomial.natDegree_zero]
      omega)
  have hpsi₂deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsine : ∀ n : ℕ, n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hpsi₂ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsideg : ∀ n : ℕ, n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree ≤ 0 + 1 :=
          Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add (Polynomial.natDegree_C _).le hpsi₂deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hmk :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hmk (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsine n (by intro h; exact hm (by simp [h])))
      (hPsideg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsine _ (Nat.succ_ne_zero n))
      (hPsideg _ (Nat.succ_ne_zero n))

private theorem ordPi_int_of_not_three_dvd (m : ℤ) (hm : ¬(3 ∣ m)) :
    ordPi (m : L) = 0 := by
  have hm0 : (m : L) ≠ 0 := by
    have hm0z : m ≠ 0 := by
      intro h
      subst m
      exact hm (dvd_zero 3)
    exact_mod_cast hm0z
  have h := vpiGood_unit m hm
  rw [vpiGood_apply_of_ne hm0] at h
  exact WithTop.coe_eq_zero.mp h

private theorem ordPi_phi_eval {n : ℕ} {x : L} (hx : ordPi x < 0) :
    ordPi ((E0Good.Φ (n : ℤ)).eval x) = ((n ^ 2 : ℕ) : ℤ) * ordPi x := by
  let p : OL[X] := E0GoodInt.Φ (n : ℤ)
  have hp : p ≠ 0 := E0GoodInt.Φ_ne_zero (n : ℤ)
  have hlc : ordPi ((p.leadingCoeff : OL) : L) = 0 := by
    rw [show p.leadingCoeff = 1 by
      simp [p, WeierstrassCurve.leadingCoeff_Φ]]
    exact ordPi_one
  have hval := ordPi_eval₂_eq_natDegree_mul p hp hx hlc
  have hdeg : p.natDegree = n ^ 2 := by
    simp [p, WeierstrassCurve.natDegree_Φ]
  rw [hdeg] at hval
  have hmap : p.eval₂ (algebraMap OL L) x = (E0Good.Φ (n : ℤ)).eval x := by
    rw [← Polynomial.eval_map]
    change ((E0GoodInt.Φ (n : ℤ)).map (algebraMap OL L)).eval x = _
    rw [← WeierstrassCurve.map_Φ, E0GoodInt_map]
  rwa [hmap] at hval

private theorem ordPi_psiSq_eval_of_unit {n : ℕ}
    (hn : ¬(3 ∣ (n : ℤ))) {x : L} (hx : ordPi x < 0) :
    ordPi ((E0Good.ΨSq (n : ℤ)).eval x) =
      (((n ^ 2 - 1 : ℕ) : ℤ) * ordPi x) := by
  let p : OL[X] := E0GoodInt.ΨSq (n : ℤ)
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (by norm_num)
  have hn0Int : (n : ℤ) ≠ 0 := by exact_mod_cast hn0
  have hn0OL : ((n : ℤ) : OL) ≠ 0 := Int.cast_ne_zero.mpr hn0Int
  have hp : p ≠ 0 := by
    exact E0GoodInt.ΨSq_ne_zero hn0OL
  have hlcEq : p.leadingCoeff = ((n : ℤ) : OL) ^ 2 := by
    simpa [p] using WeierstrassCurve.leadingCoeff_ΨSq E0GoodInt
      hn0OL
  have hnval : ordPi (n : L) = 0 :=
    ordPi_int_of_not_three_dvd (n : ℤ) hn
  have hlc : ordPi ((p.leadingCoeff : OL) : L) = 0 := by
    rw [hlcEq]
    change ordPi (algebraMap OL L (((n : ℤ) : OL) ^ 2)) = 0
    have hncast : algebraMap OL L ((n : ℤ) : OL) = (n : L) :=
      map_intCast (algebraMap OL L) (n : ℤ)
    have hnbase0 : algebraMap OL L ((n : ℤ) : OL) ≠ 0 := by
      rw [hncast]
      exact_mod_cast hn0
    rw [map_pow, ordPi_pow hnbase0, hncast, hnval]
    simp
  have hval := ordPi_eval₂_eq_natDegree_mul p hp hx hlc
  have hdeg : p.natDegree = n ^ 2 - 1 := by
    simpa [p] using WeierstrassCurve.natDegree_ΨSq E0GoodInt
      hn0OL
  rw [hdeg] at hval
  have hmap : p.eval₂ (algebraMap OL L) x =
      (E0Good.ΨSq (n : ℤ)).eval x := by
    rw [← Polynomial.eval_map]
    change ((E0GoodInt.ΨSq (n : ℤ)).map (algebraMap OL L)).eval x = _
    rw [← WeierstrassCurve.map_ΨSq, E0GoodInt_map]
  rwa [hmap] at hval

private theorem E0GoodInt_b₂_map : (E0GoodInt.b₂ : L) = E0Good.b₂ := by
  have h := congrArg WeierstrassCurve.b₂ E0GoodInt_map
  simpa only [WeierstrassCurve.map_b₂] using h

private theorem E0GoodInt_b₄_map : (E0GoodInt.b₄ : L) = E0Good.b₄ := by
  have h := congrArg WeierstrassCurve.b₄ E0GoodInt_map
  simpa only [WeierstrassCurve.map_b₄] using h

private theorem E0GoodInt_b₆_map : (E0GoodInt.b₆ : L) = E0Good.b₆ := by
  have h := congrArg WeierstrassCurve.b₆ E0GoodInt_map
  simpa only [WeierstrassCurve.map_b₆] using h

private theorem E0GoodInt_b₈_map : (E0GoodInt.b₈ : L) = E0Good.b₈ := by
  have h := congrArg WeierstrassCurve.b₈ E0GoodInt_map
  simpa only [WeierstrassCurve.map_b₈] using h

private theorem ordPi_b₄_nonneg : 0 ≤ ordPi E0Good.b₄ := by
  rw [← E0GoodInt_b₄_map]
  exact ordPi_nonneg_of_ringOfIntegers E0GoodInt.b₄

private theorem ordPi_b₆_nonneg : 0 ≤ ordPi E0Good.b₆ := by
  rw [← E0GoodInt_b₆_map]
  exact ordPi_nonneg_of_ringOfIntegers E0GoodInt.b₆

private theorem ordPi_b₈_nonneg : 0 ≤ ordPi E0Good.b₈ := by
  rw [← E0GoodInt_b₈_map]
  exact ordPi_nonneg_of_ringOfIntegers E0GoodInt.b₈

private theorem ordPi_a₂_nonneg : 0 ≤ ordPi E0Good.a₂ := by
  have ha₂map : (E0GoodInt.a₂ : L) = E0Good.a₂ := by
    have h := congrArg (fun W : WeierstrassCurve L ↦ W.a₂) E0GoodInt_map
    simpa using h
  rw [← ha₂map]
  exact ordPi_nonneg_of_ringOfIntegers E0GoodInt.a₂

/-- The `b₂` coefficient has order one.  This is the same cubic-order
certificate as `c₃`: `b₂ = c₃ + 12a₂`, and the correction has order at
least three. -/
private theorem ordPi_b₂ : ordPi E0Good.b₂ = 1 := by
  have hb₂eq : E0Good.b₂ = c₃ + 12 * E0Good.a₂ := by
    simp only [WeierstrassCurve.b₂, c₃]
    ring
  rw [hb₂eq]
  by_cases htail : (12 : L) * E0Good.a₂ = 0
  · simp [htail, ordPi_c₃]
  · have h12 : (12 : L) ≠ 0 := by norm_num
    have ha₂ : E0Good.a₂ ≠ 0 := (mul_ne_zero_iff_left h12).mp htail
    have h12ord : ordPi (12 : L) = 3 := by
      have h4ord : ordPi (4 : L) = 0 := by
        simpa only [Int.cast_ofNat] using
          ordPi_int_of_not_three_dvd (4 : ℤ) (by norm_num)
      rw [show (12 : L) = 3 * 4 by norm_num,
        ordPi_mul (by norm_num) (by norm_num), ordPi_three, h4ord]
      norm_num
    have htailOrd : 3 ≤ ordPi ((12 : L) * E0Good.a₂) := by
      rw [ordPi_mul h12 ha₂, h12ord]
      have ha₂ord := ordPi_a₂_nonneg
      omega
    rw [ordPi_add_eq_of_lt (by
      intro h
      have hv := ordPi_c₃
      rw [h, ordPi_zero] at hv
      omega) htail]
    · exact ordPi_c₃
    · rw [ordPi_c₃]
      omega

/-- The third division polynomial evaluated at `x`. -/
def psiThreeGood (x : L) : L :=
  3 * x ^ 4 + E0Good.b₂ * x ^ 3 + 3 * E0Good.b₄ * x ^ 2 +
    3 * E0Good.b₆ * x + E0Good.b₈

theorem psiThreeGood_eq_eval (x : L) :
    psiThreeGood x = E0Good.Ψ₃.eval x := by
  simp [psiThreeGood, WeierstrassCurve.Ψ₃]

/-- At formal level `r ≥ 2`, the leading term `3x⁴` strictly dominates
the third division polynomial. -/
private theorem ordPi_psiThreeGood {x : L} {r : ℤ}
    (hx : ordPi x = -2 * r) (hr : 2 ≤ r) :
    ordPi (psiThreeGood x) = 3 - 8 * r := by
  have hxneg : ordPi x < 0 := by omega
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hx
    omega
  let lead : L := 3 * x ^ 4
  let tail : List L :=
    [E0Good.b₂ * x ^ 3,
      3 * E0Good.b₄ * x ^ 2,
      3 * E0Good.b₆ * x,
      E0Good.b₈]
  have hlead0 : lead ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
  have hleadOrd : ordPi lead = 3 - 8 * r := by
    rw [ordPi_mul (by norm_num) (pow_ne_zero 4 hx0), ordPi_three,
      ordPi_pow hx0, hx]
    ring
  have htail : tail.sum = 0 ∨ ordPi lead < ordPi tail.sum := by
    apply List.recOn (motive := fun l ↦
      (∀ z ∈ l, z ≠ 0 → ordPi lead < ordPi z) →
        l.sum = 0 ∨ ordPi lead < ordPi l.sum) tail
    · simp
    · intro z l ih hall
      have hz := hall z (by simp)
      have hl : ∀ w ∈ l, w ≠ 0 → ordPi lead < ordPi w := by
        intro w hw
        exact hall w (by simp [hw])
      rcases ih hl with hzero | hsum
      · by_cases hz0 : z = 0
        · left
          simp [hz0, hzero]
        · right
          simpa [hzero] using hz hz0
      · by_cases hz0 : z = 0
        · right
          simpa [hz0] using hsum
        · by_cases hs0 : l.sum = 0
          · right
            simpa [hs0] using hz hz0
          · by_cases hadd : z + l.sum = 0
            · left
              simpa using hadd
            · right
              exact lt_of_lt_of_le (lt_min (hz hz0) hsum)
                (ordPi_add_ge hz0 hs0 hadd)
    intro z hz hz0
    simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have hb₂0 : E0Good.b₂ ≠ 0 := by
        intro h
        have hv := ordPi_b₂
        rw [h, ordPi_zero] at hv
        omega
      rw [ordPi_mul hb₂0 (pow_ne_zero 3 hx0), ordPi_b₂,
        ordPi_pow hx0, hx, hleadOrd]
      omega
    · have hb₄ : E0Good.b₄ ≠ 0 := by
        exact (mul_ne_zero_iff_left (by norm_num : (3 : L) ≠ 0)).mp
          ((mul_ne_zero_iff_right (pow_ne_zero 2 hx0)).mp hz0)
      rw [ordPi_mul (mul_ne_zero (by norm_num) hb₄) (pow_ne_zero 2 hx0),
        ordPi_mul (by norm_num) hb₄, ordPi_three, ordPi_pow hx0, hx,
        hleadOrd]
      have hb₄ord := ordPi_b₄_nonneg
      omega
    · have hb₆ : E0Good.b₆ ≠ 0 := by
        exact (mul_ne_zero_iff_left (by norm_num : (3 : L) ≠ 0)).mp
          ((mul_ne_zero_iff_right hx0).mp hz0)
      rw [ordPi_mul (mul_ne_zero (by norm_num) hb₆) hx0,
        ordPi_mul (by norm_num) hb₆, ordPi_three, hx, hleadOrd]
      have hb₆ord := ordPi_b₆_nonneg
      omega
    · rw [hleadOrd]
      have hb₈ord := ordPi_b₈_nonneg
      omega
  have hshape : psiThreeGood x = lead + tail.sum := by
    simp [psiThreeGood, lead, tail]
    ring
  rw [hshape]
  rcases htail with htail | htail
  · simp [htail, hleadOrd]
  · by_cases htail0 : tail.sum = 0
    · simp [htail0, hleadOrd]
    · rw [ordPi_add_eq_of_lt hlead0 htail0 htail, hleadOrd]

private theorem ordPi_psiSq_three {x : L} {r : ℤ}
    (hx : ordPi x = -2 * r) (hr : 2 ≤ r) :
    ordPi ((E0Good.ΨSq (3 : ℤ)).eval x) = 6 - 16 * r := by
  have hpsi := ordPi_psiThreeGood hx hr
  have hpsi0 : psiThreeGood x ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hpsi
    omega
  have heval : (E0Good.ΨSq (3 : ℤ)).eval x = psiThreeGood x ^ 2 := by
    change (E0Good.ΨSq (3 : ℕ)).eval x = _
    rw [E0Good.ΨSq_ofNat 3]
    simp [show ¬Even (3 : ℕ) by decide,
      WeierstrassCurve.preΨ'_three, ← psiThreeGood_eq_eval]
  rw [heval, ordPi_pow hpsi0, hpsi]
  ring

/-! ## Scalar-multiplication coordinates -/

private theorem xPair_same_nsmul {n : ℕ} {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y) :
    KeystoneLadder.SameP1Vec
      ((n • (WeierstrassCurve.Affine.Point.some x y h : E0GoodPoint)).xRep)
      (KeystoneLadder.xPair E0Good (n : ℤ) x) := by
  letI : DecidableEq L := Classical.decEq L
  have hbase : (E0Good⁄L).Nonsingular x y := by
    simpa [WeierstrassCurve.baseChange] using h
  have hh : hbase = h := Subsingleton.elim _ _
  have hs₁ := KeystoneLadder.XOnly.xLadderRep_correct_seam
    (E := E0Good⁄L) hbase n
  have hs₂ := KeystoneLadder.xPair_same_xLadderRep_seam E0Good n x
    (by norm_num) (psi_ne_zero_charZero E0Good)
    (WeierstrassCurve.Ψ₃_ne_zero E0Good (by norm_num))
  rw [hh] at hs₁
  exact KeystoneLadder.SameP1Vec.trans
    hs₁
    (by simpa [WeierstrassCurve.baseChange] using hs₂)

private theorem nsmul_affine_x_eq_div {n : ℕ} {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hden : (E0Good.ΨSq (n : ℤ)).eval x ≠ 0) :
    ∃ (xn yn : L) (hn : WeierstrassCurve.Affine.Nonsingular E0Good xn yn),
      n • (WeierstrassCurve.Affine.Point.some x y h : E0GoodPoint) =
          WeierstrassCurve.Affine.Point.some xn yn hn ∧
        xn = (E0Good.Φ (n : ℤ)).eval x /
          (E0Good.ΨSq (n : ℤ)).eval x := by
  classical
  have hs := xPair_same_nsmul (n := n) h
  generalize hQ : n •
      (WeierstrassCurve.Affine.Point.some x y h : E0GoodPoint) = Q at hs
  cases Q with
  | zero =>
      change KeystoneLadder.SameP1Vec ![1, 0]
        (KeystoneLadder.xPair E0Good (n : ℤ) x) at hs
      have hzero := KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty
        (v := KeystoneLadder.xPair E0Good (n : ℤ) x) hs
      exact absurd (by simpa [KeystoneLadder.xPair] using hzero) hden
  | some xn yn hn =>
      refine ⟨xn, yn, hn, rfl, ?_⟩
      rcases hs with ⟨c, hc, hvec⟩
      have hnum : (E0Good.Φ (n : ℤ)).eval x = c * xn := by
        have := congrFun hvec 0
        simpa [KeystoneLadder.xPair, hQ, Pi.smul_apply] using this
      have hdenEq : (E0Good.ΨSq (n : ℤ)).eval x = c := by
        have := congrFun hvec 1
        simpa [KeystoneLadder.xPair, hQ, Pi.smul_apply] using this
      rw [hnum, hdenEq]
      field_simp

private theorem affine_val_coords {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : ordPi x < 0) :
    ordPi x = -2 * ordPi (-x / y) ∧
      ordPi y = -3 * ordPi (-x / y) := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hx
    omega
  have hy0 : y ≠ 0 := by
    intro hzero
    subst y
    have heq := (WeierstrassCurve.Affine.equation_iff x 0).mp h.1
    let p : OL[X] := X ^ 3 + C E0GoodInt.a₂ * X ^ 2 +
      C E0GoodInt.a₄ * X + C E0GoodInt.a₆
    have hp : p ≠ 0 := by
      intro hp0
      have hcoeff := congrArg (fun q : OL[X] ↦ q.coeff 3) hp0
      simp [p] at hcoeff
    have hlc : ordPi ((p.leadingCoeff : OL) : L) = 0 := by
      have hlcEq : p.leadingCoeff = 1 := by
        simpa [p] using
          (Polynomial.leadingCoeff_cubic
            (R := OL) (a := (1 : OL)) (b := E0GoodInt.a₂)
            (c := E0GoodInt.a₄) (d := E0GoodInt.a₆) one_ne_zero)
      rw [hlcEq]
      simpa using ordPi_one
    have hpval := ordPi_eval₂_eq_natDegree_mul p hp hx hlc
    have hpdeg : p.natDegree = 3 := by
      simpa [p] using
        (Polynomial.natDegree_cubic
          (R := OL) (a := (1 : OL)) (b := E0GoodInt.a₂)
          (c := E0GoodInt.a₄) (d := E0GoodInt.a₆) one_ne_zero)
    have hpzero : p.eval₂ (algebraMap OL L) x = 0 := by
      have ha₂map : algebraMap OL L E0GoodInt.a₂ = E0Good.a₂ := by
        have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₂) E0GoodInt_map
        simpa only [WeierstrassCurve.map_a₂] using hm
      have ha₄map : algebraMap OL L E0GoodInt.a₄ = E0Good.a₄ := by
        have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₄) E0GoodInt_map
        simpa only [WeierstrassCurve.map_a₄] using hm
      have ha₆map : algebraMap OL L E0GoodInt.a₆ = E0Good.a₆ := by
        have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₆) E0GoodInt_map
        simpa only [WeierstrassCurve.map_a₆] using hm
      dsimp [p]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      rw [ha₂map, ha₄map, ha₆map]
      change x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ = 0
      norm_num at heq
      exact heq.symm
    rw [hpzero, ordPi_zero, hpdeg] at hpval
    omega
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  exact GoodModel.val_coords hx0 hy0 (by simpa using heq) hx

/-! ## Prime-to-three scalar multiplication -/

private theorem unit_nsmul_data (n : ℕ) (hn : ¬(3 ∣ (n : ℤ)))
    {P : E0GoodPoint} (hP : InFormalKernel P) :
    InFormalKernel (n • P) ∧
      ordPi (zParamGood (n • P)) = ordPi (zParamGood P) := by
  cases P with
  | zero =>
      change InFormalKernel (n • (0 : E0GoodPoint)) ∧
        ordPi (zParamGood (n • (0 : E0GoodPoint))) =
          ordPi (zParamGood (0 : E0GoodPoint))
      have hnzero : n • (0 : E0GoodPoint) = 0 := nsmul_zero n
      rw [hnzero]
      exact ⟨trivial, rfl⟩
  | some x y h =>
      simp only [InFormalKernel] at hP
      have hx0 : x ≠ 0 := by
        intro hzero
        rw [hzero, ordPi_zero] at hP
        omega
      have hnumOrd := ordPi_phi_eval (n := n) hP
      have hdenOrd := ordPi_psiSq_eval_of_unit (n := n) hn hP
      have hden0 : (E0Good.ΨSq (n : ℤ)).eval x ≠ 0 := by
        by_cases hn1 : n = 1
        · subst n
          norm_num [WeierstrassCurve.ΨSq]
        · intro hzero
          rw [hzero, ordPi_zero] at hdenOrd
          have hn0 : n ≠ 0 := by
            intro hnzero
            subst n
            exact hn (by norm_num)
          have hn2 : 2 ≤ n := by omega
          have hcoef : 0 < ((n ^ 2 - 1 : ℕ) : ℤ) := by
            exact_mod_cast (Nat.sub_pos_of_lt (by nlinarith : 1 < n ^ 2))
          nlinarith
      obtain ⟨xn, yn, hQ, hpoint, hxn⟩ := nsmul_affine_x_eq_div h hden0
      have hnum0 : (E0Good.Φ (n : ℤ)).eval x ≠ 0 := by
        intro hzero
        rw [hzero, ordPi_zero] at hnumOrd
        have hn0 : n ≠ 0 := by
          intro hnzero
          subst n
          exact hn (by norm_num)
        have hn2pos : 0 < ((n ^ 2 : ℕ) : ℤ) := by positivity
        nlinarith
      have hxnOrd : ordPi xn = ordPi x := by
        rw [hxn, ordPi_div hnum0 hden0, hnumOrd, hdenOrd]
        have hn0 : n ≠ 0 := by
          intro hnzero
          subst n
          exact hn (by norm_num)
        have hn2 : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hn0)
        rw [Nat.cast_sub hn2]
        ring
      have hxnNeg : ordPi xn < 0 := by rw [hxnOrd]; exact hP
      have hin := affine_val_coords h hP
      have hout := affine_val_coords hQ hxnNeg
      constructor
      · rw [hpoint]
        exact hxnNeg
      · rw [hpoint, zParamGood_some, zParamGood_some]
        rw [hxnOrd] at hout
        omega

/-- `3 ∤ n` implies that `[n]` preserves the good formal parameter order. -/
theorem val_unit_smul (n : ℕ) (hn : ¬(3 ∣ (n : ℤ)))
    {P : E0GoodPoint} (hP : InFormalKernel P) :
    ordPi (zParamGood (n • P)) = ordPi (zParamGood P) :=
  (unit_nsmul_data n hn hP).2

/-! ## Exact tripling at level at least two -/

private theorem three_nsmul_data {P : E0GoodPoint}
    (hP : InFormalKernel P) (hz : zParamGood P ≠ 0)
    (hlevel : 2 ≤ ordPi (zParamGood P)) :
    InFormalKernel (3 • P) ∧ zParamGood (3 • P) ≠ 0 ∧
      ordPi (zParamGood (3 • P)) = 3 + ordPi (zParamGood P) := by
  cases P with
  | zero => exact absurd rfl hz
  | some x y h =>
      simp only [InFormalKernel] at hP
      let r := ordPi (-x / y)
      have hin := affine_val_coords h hP
      have hxr : ordPi x = -2 * r := by simpa [r] using hin.1
      have hr : 2 ≤ r := by simpa [zParamGood_some, r] using hlevel
      have hnumOrd := ordPi_phi_eval (n := 3) hP
      have hdenOrd := ordPi_psiSq_three hxr hr
      have hden0 : (E0Good.ΨSq (3 : ℤ)).eval x ≠ 0 := by
        intro hzero
        rw [hzero, ordPi_zero] at hdenOrd
        omega
      obtain ⟨xn, yn, hQ, hpoint, hxn⟩ := nsmul_affine_x_eq_div h hden0
      have hdenOrdNat :
          ordPi ((E0Good.ΨSq ((3 : ℕ) : ℤ)).eval x) = 6 - 16 * r := by
        simpa only [Nat.cast_ofNat] using hdenOrd
      have hden0Nat : (E0Good.ΨSq ((3 : ℕ) : ℤ)).eval x ≠ 0 := by
        simpa only [Nat.cast_ofNat] using hden0
      have hnum0 : (E0Good.Φ ((3 : ℕ) : ℤ)).eval x ≠ 0 := by
        intro hzero
        rw [hzero, ordPi_zero, hxr] at hnumOrd
        omega
      have hxnOrd : ordPi xn = -2 * (r + 3) := by
        rw [hxn, ordPi_div hnum0 hden0Nat, hnumOrd, hdenOrdNat, hxr]
        ring
      have hxnNeg : ordPi xn < 0 := by omega
      have hout := affine_val_coords hQ hxnNeg
      have hzoutOrd : ordPi (-xn / yn) = r + 3 := by
        rw [hxnOrd] at hout
        omega
      constructor
      · rw [hpoint]
        exact hxnNeg
      constructor
      · rw [hpoint, zParamGood_some]
        intro hzero
        rw [hzero, ordPi_zero] at hzoutOrd
        omega
      · rw [hpoint, zParamGood_some, zParamGood_some]
        simpa [r, add_comm] using hzoutOrd

/-- If `P` is in the good formal kernel and `ordPi z(P) ≥ 2`, then
tripling raises its parameter order by exactly three. -/
theorem ordPi_three_smul_eq {P : E0GoodPoint}
    (hP : InFormalKernel P) (hlevel : 2 ≤ ordPi (zParamGood P)) :
    ordPi (zParamGood (3 • P)) = 3 + ordPi (zParamGood P) := by
  have hz : zParamGood P ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hlevel
    omega
  exact (three_nsmul_data hP hz hlevel).2.2

private theorem three_pow_nsmul_data {P : E0GoodPoint}
    (hP : InFormalKernel P) (hz : zParamGood P ≠ 0)
    (hlevel : 2 ≤ ordPi (zParamGood P)) (j : ℕ) :
    InFormalKernel ((3 ^ j) • P) ∧ zParamGood ((3 ^ j) • P) ≠ 0 ∧
      ordPi (zParamGood ((3 ^ j) • P)) =
        3 * (j : ℤ) + ordPi (zParamGood P) := by
  induction j with
  | zero => exact ⟨by simpa, by simpa, by simp⟩
  | succ j ih =>
      rcases ih with ⟨hjP, hjz, hjord⟩
      have hjlevel : 2 ≤ ordPi (zParamGood ((3 ^ j) • P)) := by
        rw [hjord]
        omega
      have hthree := three_nsmul_data hjP hjz hjlevel
      have hpow : (3 ^ (j + 1)) • P = 3 • ((3 ^ j) • P) := by
        rw [pow_succ, mul_nsmul]
      rw [hpow]
      refine ⟨hthree.1, hthree.2.1, ?_⟩
      rw [hthree.2.2, hjord]
      push_cast
      ring

/-! ## Torsion exclusion -/

/-- The second formal-kernel step contains no point of positive finite order. -/
theorem msq_torsionFree {P : E0GoodPoint}
    (hP : InFormalKernel P) (hlevel : 2 ≤ ordPi (zParamGood P)) :
    ¬∃ n : ℕ, 0 < n ∧ n • P = 0 := by
  have hz : zParamGood P ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hlevel
    omega
  rintro ⟨n, hnpos, hnP⟩
  obtain ⟨j, m, hm3, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hnpos.ne' 3 (by norm_num)
  have hj := three_pow_nsmul_data hP hz hlevel j
  let Q : E0GoodPoint := (3 ^ j) • P
  have hQ : InFormalKernel Q := by simpa [Q] using hj.1
  have hQz : zParamGood Q ≠ 0 := by simpa [Q] using hj.2.1
  have hm3z : ¬(3 ∣ (m : ℤ)) := by exact_mod_cast hm3
  have hunit := unit_nsmul_data m hm3z hQ
  have hmQz : zParamGood (m • Q) ≠ 0 := by
    intro hzero
    have hval := hunit.2
    rw [hzero, ordPi_zero] at hval
    have hQord : 2 ≤ ordPi (zParamGood Q) := by
      simpa [Q, hj.2.2] using
        (show 2 ≤ 3 * (j : ℤ) + ordPi (zParamGood P) by omega)
    omega
  have hmQ : m • Q = 0 := by
    dsimp [Q]
    rw [← mul_nsmul, ← hnm, hnP]
  apply hmQz
  rw [hmQ, zParamGood_zero]

/-- A nonzero torsion point in the good formal kernel has parameter order
exactly one.  Equivalently, no torsion survives in `m²`. -/
theorem torsion_val_eq_one (P : E0GoodPoint)
    (hP : InFormalKernel P) (hz : zParamGood P ≠ 0)
    (htor : ∃ n : ℕ, 0 < n ∧ n • P = 0) :
    ordPi (zParamGood P) = 1 := by
  have hpos : 0 < ordPi (zParamGood P) := by
    cases P with
    | zero => exact absurd rfl hz
    | some x y h =>
        simp only [InFormalKernel] at hP
        have hv := affine_val_coords h hP
        simp only [zParamGood_some]
        omega
  by_contra hne
  have hlevel : 2 ≤ ordPi (zParamGood P) := by omega
  exact msq_torsionFree hP hlevel htor

end

end MazurProof.N18PackageII
