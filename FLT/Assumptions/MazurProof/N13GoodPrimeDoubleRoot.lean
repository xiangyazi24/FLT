import FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot

/-!
# The leading-unit double-root branch at an N13 good prime

After the simple-root argument, local primitivity leaves one quadratic
configuration: the leading coefficient is a unit and the branch point is a
double root modulo the maximal ideal.

For a locally primitive homogeneous pair `(scale, V)`, if the scale is not
a unit then the degree-at-most-one polynomial `V` is primitive.  Since its
value at the double root is small, its derivative is a unit.  Differentiating
the homogeneous Mumford relation twice then shows that the complementary
factor `W` is a unit at the branch point.  Evaluation of the original
relation therefore writes the quadratic Kummer value as a unit times a
square.

No residue-field elements, prime ideals, or candidate squareclasses are
enumerated.
-/

open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring

namespace MazurProof.N13GoodPrimeDoubleRoot

noncomputable section

open N13GoodPrimeSimpleRoot

/-- A primitive linear polynomial which is small at a local point has unit
derivative there. -/
theorem linear_derivative_isUnit_of_content_top_small
    {R : Type*} [CommRing R] [IsLocalRing R]
    (V : R[X]) (hdeg : V.natDegree ≤ 1)
    (hcontent : V.contentIdeal = ⊤)
    (x : R)
    (hsmall :
      V.eval x ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (V.derivative.eval x) := by
  let d := V.coeff 1
  let e := V.coeff 0
  have hcoeff2 :
      V.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (hdeg.trans_lt (by omega))
  have hV :
      V = quadratic 0 d e := by
    have h :=
      eq_quadratic_of_natDegree_le_two
        V (hdeg.trans (by omega))
    simpa only [d, e, hcoeff2] using h
  have hderivative :
      V.derivative.eval x = d := by
    rw [hV]
    simp
  rw [hderivative]
  by_contra hd
  have hd_mem :
      d ∈ IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hd
  have hsmall' :
      d * x + e ∈
        IsLocalRing.maximalIdeal R := by
    rw [hV] at hsmall
    simpa using hsmall
  have hdx_mem :
      d * x ∈
        IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right
      x hd_mem
  have he_mem :
      e ∈ IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).sub_mem
        hsmall' hdx_mem
    convert this using 1
    ring
  have hle :
      V.contentIdeal ≤
        IsLocalRing.maximalIdeal R := by
    rw [Polynomial.contentIdeal_def,
      Ideal.span_le]
    intro z hz
    obtain ⟨n, -, rfl⟩ :=
      Polynomial.mem_coeffs_iff.mp hz
    rw [hV]
    by_cases hn0 : n = 0
    · subst n
      simpa [quadratic] using he_mem
    by_cases hn1 : n = 1
    · subst n
      simpa [quadratic] using hd_mem
    simp [quadratic, coeff_C, coeff_X,
      hn0, Ne.symm hn1]
  have htop :
      (⊤ : Ideal R) ≤
        IsLocalRing.maximalIdeal R := by
    rw [← hcontent]
    exact hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_unique htop)

/-- The exact second-derivative identity used in the double-root branch. -/
theorem secondDerivative_homogeneous_relation
    {R : Type*} [CommRing R]
    (a b c x scale : R)
    (F V W : R[X])
    (hVdeg : V.natDegree ≤ 1)
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    scale ^ 2 * F.derivative.derivative.eval x -
        2 * (V.derivative.eval x) ^ 2 =
      (2 * a) * W.eval x +
        2 * (2 * a * x + b) *
          W.derivative.eval x +
        (a * x ^ 2 + b * x + c) *
          W.derivative.derivative.eval x := by
  have hcoeff2 :
      V.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (hVdeg.trans_lt (by omega))
  have hV :
      V =
        quadratic 0 (V.coeff 1) (V.coeff 0) := by
    have h :=
      eq_quadratic_of_natDegree_le_two
        V (hVdeg.trans (by omega))
    simpa only [hcoeff2] using h
  have h :=
    congrArg (Polynomial.eval x)
      (congrArg Polynomial.derivative
        (congrArg Polynomial.derivative hrelation))
  rw [hV] at h ⊢
  simp only [quadratic] at h ⊢
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow, derivative_C,
    derivative_X,
    zero_mul, mul_zero, zero_add, add_zero,
    mul_one, eval_sub, eval_add, eval_mul,
    eval_C, eval_X] at h ⊢
  simp at h ⊢
  ring_nf at h ⊢
  exact h

/-- In the leading-unit double-root regime, a primitive linear companion
forces the complementary factor to be a unit at the branch point. -/
theorem W_eval_isUnit_of_leading_doubleRoot
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    (a b c x scale : R)
    (F V W : R[X])
    (htwo : IsUnit (2 : R))
    (hscale : ¬ IsUnit scale)
    (hsmall :
      a * x ^ 2 + b * x + c ∈
        IsLocalRing.maximalIdeal R)
    (hnonsimple :
      ¬ IsUnit (2 * a * x + b))
    (hVdeg : V.natDegree ≤ 1)
    (hVcontent : V.contentIdeal = ⊤)
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    IsUnit (W.eval x) := by
  let m : Ideal R :=
    IsLocalRing.maximalIdeal R
  have hscale_mem : scale ∈ m := by
    simpa only [m, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hscale
  have hderiv_mem :
      2 * a * x + b ∈ m := by
    simpa only [m, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hnonsimple
  have hscale_sq_mem :
      scale ^ 2 ∈ m := by
    simpa only [pow_two] using
      m.mul_mem_right scale hscale_mem
  have hscale_term :
      scale ^ 2 * F.eval x ∈ m :=
    m.mul_mem_right (F.eval x) hscale_sq_mem
  have hUW :
      (a * x ^ 2 + b * x + c) *
          W.eval x ∈ m :=
    m.mul_mem_right (W.eval x) hsmall
  have heval :=
    congrArg (Polynomial.eval x) hrelation
  simp only [eval_sub, eval_mul, eval_pow,
    eval_C, quadratic_eval] at heval
  have hVsq :
      (V.eval x) ^ 2 ∈ m := by
    have heq :
        (V.eval x) ^ 2 =
          scale ^ 2 * F.eval x -
            (a * x ^ 2 + b * x + c) *
              W.eval x := by
      calc
        (V.eval x) ^ 2 =
            scale ^ 2 * F.eval x -
              (scale ^ 2 * F.eval x -
                (V.eval x) ^ 2) := by
          ring
        _ =
            scale ^ 2 * F.eval x -
              (a * x ^ 2 + b * x + c) *
                W.eval x := by
          rw [heval]
    rw [heq]
    exact m.sub_mem hscale_term hUW
  have hVsmall :
      V.eval x ∈ m :=
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime
      |>.mem_of_pow_mem 2 hVsq
  have hVprime :
      IsUnit (V.derivative.eval x) :=
    linear_derivative_isUnit_of_content_top_small
      V hVdeg hVcontent x hVsmall
  have hsecond :=
    secondDerivative_homogeneous_relation
      a b c x scale F V W hVdeg hrelation
  have hA :
      scale ^ 2 *
          F.derivative.derivative.eval x ∈ m :=
    m.mul_mem_right
      (F.derivative.derivative.eval x)
      hscale_sq_mem
  have hD :
      2 * (2 * a * x + b) *
          W.derivative.eval x ∈ m := by
    have :=
      m.mul_mem_left 2 hderiv_mem
    exact
      m.mul_mem_right
        (W.derivative.eval x) this
  have hE :
      (a * x ^ 2 + b * x + c) *
          W.derivative.derivative.eval x ∈ m :=
    m.mul_mem_right
      (W.derivative.derivative.eval x)
      hsmall
  have hdelta :
      (2 * a) * W.eval x -
          (-(2 * (V.derivative.eval x) ^ 2)) ∈ m := by
    have heq :
        (2 * a) * W.eval x -
            (-(2 * (V.derivative.eval x) ^ 2)) =
          scale ^ 2 *
              F.derivative.derivative.eval x -
            2 * (2 * a * x + b) *
              W.derivative.eval x -
            (a * x ^ 2 + b * x + c) *
              W.derivative.derivative.eval x := by
      calc
        (2 * a) * W.eval x -
              (-(2 * (V.derivative.eval x) ^ 2)) =
            ((2 * a) * W.eval x +
                2 * (2 * a * x + b) *
                  W.derivative.eval x +
                (a * x ^ 2 + b * x + c) *
                  W.derivative.derivative.eval x) +
              2 * (V.derivative.eval x) ^ 2 -
              2 * (2 * a * x + b) *
                W.derivative.eval x -
              (a * x ^ 2 + b * x + c) *
                W.derivative.derivative.eval x := by
          ring
        _ =
            (scale ^ 2 *
                F.derivative.derivative.eval x -
              2 * (V.derivative.eval x) ^ 2) +
              2 * (V.derivative.eval x) ^ 2 -
              2 * (2 * a * x + b) *
                W.derivative.eval x -
              (a * x ^ 2 + b * x + c) *
                W.derivative.derivative.eval x := by
          rw [hsecond]
        _ =
            scale ^ 2 *
                F.derivative.derivative.eval x -
              2 * (2 * a * x + b) *
                W.derivative.eval x -
              (a * x ^ 2 + b * x + c) *
                W.derivative.derivative.eval x := by
          ring
    rw [heq]
    exact m.sub_mem (m.sub_mem hA hD) hE
  have hbase :
      IsUnit
        (-(2 * (V.derivative.eval x) ^ 2)) :=
    (htwo.mul (hVprime.pow 2)).neg
  have hproduct :
      IsUnit ((2 * a) * W.eval x) := by
    have heq :
        (2 * a) * W.eval x =
          -(2 * (V.derivative.eval x) ^ 2) +
            ((2 * a) * W.eval x -
              (-(2 * (V.derivative.eval x) ^ 2))) := by
      ring
    rw [heq]
    exact
      isUnit_add_of_mem_henselianIdeal
        m hbase hdelta
  exact isUnit_of_mul_isUnit_right hproduct

/-- Unit-times-square conclusion of the normalized double-root argument. -/
theorem quadratic_eval_eq_unit_mul_sq_of_doubleRoot
    {R K : Type*}
    [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (a b c x scale : R)
    (F V W : R[X])
    (htwo : IsUnit (2 : R))
    (hscale : ¬ IsUnit scale)
    (hsmall :
      a * x ^ 2 + b * x + c ∈
        IsLocalRing.maximalIdeal R)
    (hnonsimple :
      ¬ IsUnit (2 * a * x + b))
    (hVdeg : V.natDegree ≤ 1)
    (hVcontent : V.contentIdeal = ⊤)
    (hFroot : F.eval x = 0)
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K
          (a * x ^ 2 + b * x + c) =
        algebraMap R K (u : R) * z ^ 2 := by
  have hW :
      IsUnit (W.eval x) :=
    W_eval_isUnit_of_leading_doubleRoot
      a b c x scale F V W htwo hscale
      hsmall hnonsimple hVdeg hVcontent hrelation
  let wUnit : Rˣ := hW.unit
  let u : Rˣ := -wUnit⁻¹
  let z : K :=
    algebraMap R K (V.eval x)
  have heval :=
    congrArg (Polynomial.eval x) hrelation
  simp only [eval_sub, eval_mul, eval_pow,
    eval_C, quadratic_eval, hFroot, mul_zero,
    zero_sub] at heval
  have hU :
      a * x ^ 2 + b * x + c =
        (u : R) * (V.eval x) ^ 2 := by
    calc
      a * x ^ 2 + b * x + c =
          ((a * x ^ 2 + b * x + c) *
            W.eval x) *
              ((wUnit⁻¹ : Rˣ) : R) := by
        rw [← hW.unit_spec]
        rw [mul_assoc, ← Units.val_mul]
        simp [wUnit]
      _ =
          (-(V.eval x) ^ 2) *
            ((wUnit⁻¹ : Rˣ) : R) := by
        rw [← heval]
      _ =
          (u : R) * (V.eval x) ^ 2 := by
        simp [u]
        ring
  refine ⟨u, z, ?_⟩
  have hmap :=
    congrArg (algebraMap R K) hU
  simpa only [z, map_mul, map_pow] using hmap

/-- Completion form of the normalized double-root principle. -/
theorem multiplicity_even_of_completion_quadratic_doubleRoot
    {A K : Type*}
    [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsDedekindDomain A]
    (v : HeightOneSpectrum A)
    {global : A} (hglobal_ne : global ≠ 0)
    (a b c x scale :
      v.adicCompletionIntegers K)
    (F V W :
      (v.adicCompletionIntegers K)[X])
    (hglobal :
      algebraMap A (v.adicCompletion K) global =
        ((a * x ^ 2 + b * x + c :
            v.adicCompletionIntegers K) :
          v.adicCompletion K))
    (htwo :
      IsUnit (2 : v.adicCompletionIntegers K))
    (hscale : ¬ IsUnit scale)
    (hsmall :
      a * x ^ 2 + b * x + c ∈
        v.completionIdeal K)
    (hnonsimple :
      ¬ IsUnit (2 * a * x + b))
    (hVdeg : V.natDegree ≤ 1)
    (hVcontent : V.contentIdeal = ⊤)
    (hFroot : F.eval x = 0)
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {global})) := by
  letI :
      HenselianRing
        (v.adicCompletionIntegers K)
        (v.completionIdeal K) :=
    N13GoodPrimeCompletion.completionIntegers_henselianRing
      v
  obtain ⟨u, z, huz⟩ :=
    quadratic_eval_eq_unit_mul_sq_of_doubleRoot
      (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K)
      a b c x scale F V W htwo hscale hsmall
      hnonsimple hVdeg hVcontent hFroot hrelation
  apply
    N13GoodPrimeCompletion.multiplicity_even_of_completion_eq_unit_mul_sq
      v hglobal_ne u z
  change
    algebraMap A (v.adicCompletion K) global =
      algebraMap
          (v.adicCompletionIntegers K)
          (v.adicCompletion K) (u :
            v.adicCompletionIntegers K) *
        z ^ 2
  rw [hglobal]
  exact huz

end

end MazurProof.N13GoodPrimeDoubleRoot
