import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# A6 height prototype

This file is intentionally standalone. It prototypes the algebraic backbone for
the duplication-map height argument without importing or wiring into the FLT
torsion files.
-/

open Polynomial

namespace WeierstrassCurve.HeightDoubling

noncomputable section

variable {R : Type*} [CommRing R]

def dupNumPoly (W : WeierstrassCurve R) : Polynomial R :=
  monomial 4 1 - monomial 2 W.b₄ - monomial 1 (2 * W.b₆) - C W.b₈

def dupDenPoly (W : WeierstrassCurve R) : Polynomial R :=
  monomial 3 4 + monomial 2 W.b₂ + monomial 1 (2 * W.b₄) + C W.b₆

def dupNumH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  X ^ 4 - W.b₄ * X ^ 2 * Z ^ 2 - 2 * W.b₆ * X * Z ^ 3 - W.b₈ * Z ^ 4

def dupDenH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  4 * X ^ 3 * Z + W.b₂ * X ^ 2 * Z ^ 2 + 2 * W.b₄ * X * Z ^ 3 + W.b₆ * Z ^ 4

namespace DupResultantUniversal

abbrev S := MvPolynomial (Fin 4) ℤ

def B2 : S := MvPolynomial.X 0
def B4 : S := MvPolynomial.X 1
def B6 : S := MvPolynomial.X 2
def B8 : S := MvPolynomial.X 3

def F : Polynomial S :=
  X ^ 4 - C B4 * X ^ 2 - C (2 * B6) * X - C B8

def G : Polynomial S :=
  C 4 * X ^ 3 + C B2 * X ^ 2 + C (2 * B4) * X + C B6

def rawRes : S :=
  B2 ^ 4 * B8 ^ 2
    - 6 * B2 ^ 3 * B4 * B6 * B8
    + 4 * B2 ^ 3 * B6 ^ 3
    + 4 * B2 ^ 2 * B4 ^ 3 * B8
    - 3 * B2 ^ 2 * B4 ^ 2 * B6 ^ 2
    - 48 * B2 ^ 2 * B4 * B8 ^ 2
    + 6 * B2 ^ 2 * B6 ^ 2 * B8
    + 240 * B2 * B4 ^ 2 * B6 * B8
    - 162 * B2 * B4 * B6 ^ 3
    + 192 * B2 * B6 * B8 ^ 2
    - 144 * B4 ^ 4 * B8
    + 108 * B4 ^ 3 * B6 ^ 2
    + 384 * B4 ^ 2 * B8 ^ 2
    - 1296 * B4 * B6 ^ 2 * B8
    + 729 * B6 ^ 4
    - 256 * B8 ^ 3

end DupResultantUniversal

def dupNumPolyB (b4 b6 b8 : ℚ) : Polynomial ℚ :=
  monomial 4 1 - monomial 2 b4 - monomial 1 (2 * b6) - C b8

def dupDenPolyB (b2 b4 b6 : ℚ) : Polynomial ℚ :=
  monomial 3 4 + monomial 2 b2 + monomial 1 (2 * b4) + C b6

def quotientPolyB (b2 : ℚ) : Polynomial ℚ :=
  monomial 1 (-(1 / 4 : ℚ)) + C (b2 / 16)

def reducedNumPolyB (b2 b4 b6 b8 : ℚ) : Polynomial ℚ :=
  monomial 2 (b2 ^ 2 / 16 - 3 * b4 / 2)
    + monomial 1 (b2 * b4 / 8 - 9 * b6 / 4)
    + C (b2 * b6 / 16 - b8)

abbrev rawResB (b2 b4 b6 b8 : ℚ) : ℚ :=
  b2 ^ 4 * b8 ^ 2
    - 6 * b2 ^ 3 * b4 * b6 * b8
    + 4 * b2 ^ 3 * b6 ^ 3
    + 4 * b2 ^ 2 * b4 ^ 3 * b8
    - 3 * b2 ^ 2 * b4 ^ 2 * b6 ^ 2
    - 48 * b2 ^ 2 * b4 * b8 ^ 2
    + 6 * b2 ^ 2 * b6 ^ 2 * b8
    + 240 * b2 * b4 ^ 2 * b6 * b8
    - 162 * b2 * b4 * b6 ^ 3
    + 192 * b2 * b6 * b8 ^ 2
    - 144 * b4 ^ 4 * b8
    + 108 * b4 ^ 3 * b6 ^ 2
    + 384 * b4 ^ 2 * b8 ^ 2
    - 1296 * b4 * b6 ^ 2 * b8
    + 729 * b6 ^ 4
    - 256 * b8 ^ 3

abbrev rawResCofactor (b2 b4 b6 b8 : ℚ) : ℚ :=
  3 * b2 ^ 2 * b4 * b8
    + b2 ^ 2 * b6 ^ 2
    - 20 * b2 * b4 ^ 2 * b6
    - 8 * b2 * b6 * b8
    + 16 * b4 ^ 4
    - 28 * b4 ^ 2 * b8
    + 81 * b4 * b6 ^ 2
    + 16 * b8 ^ 2

def quadCubicSylvester (a b c d e h k : ℚ) : Matrix (Fin 5) (Fin 5) ℚ :=
  !![k, 0, c, 0, 0;
     h, k, b, c, 0;
     e, h, a, b, c;
     d, e, 0, a, b;
     0, d, 0, 0, a]

def quadCubicMinor41 (a b c d e h k : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![k, c, 0, 0;
     h, b, c, 0;
     e, a, b, c;
     d, 0, a, b]

def quadCubicMinor44 (a b c d e h k : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![k, 0, c, 0;
     h, k, b, c;
     e, h, a, b;
     d, e, 0, a]

lemma det_quadCubicSylvester
    (a b c d e h k : ℚ) :
    (quadCubicSylvester a b c d e h k).det =
      a ^ 3 * k ^ 2 - a ^ 2 * b * h * k - 2 * a ^ 2 * c * e * k
        + a ^ 2 * c * h ^ 2 + a * b ^ 2 * e * k + 3 * a * b * c * d * k
        - a * b * c * e * h - 2 * a * c ^ 2 * d * h + a * c ^ 2 * e ^ 2
        - b ^ 3 * d * k + b ^ 2 * c * d * h - b * c ^ 2 * d * e
        + c ^ 3 * d ^ 2 := by
  rw [Matrix.det_succ_row (quadCubicSylvester a b c d e h k) (4 : Fin 5)]
  simp [quadCubicSylvester, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

lemma resultant_quadratic_cubic
    (a b c d e h k : ℚ) :
    (monomial 2 a + monomial 1 b + C c).resultant
        (monomial 3 d + monomial 2 e + monomial 1 h + C k) 2 3 =
      a ^ 3 * k ^ 2 - a ^ 2 * b * h * k - 2 * a ^ 2 * c * e * k
        + a ^ 2 * c * h ^ 2 + a * b ^ 2 * e * k + 3 * a * b * c * d * k
        - a * b * c * e * h - 2 * a * c ^ 2 * d * h + a * c ^ 2 * e ^ 2
        - b ^ 3 * d * k + b ^ 2 * c * d * h - b * c ^ 2 * d * e
        + c ^ 3 * d ^ 2 := by
  have hM :
      (monomial 2 a + monomial 1 b + C c).sylvester
          (monomial 3 d + monomial 2 e + monomial 1 h + C k) 2 3 =
        quadCubicSylvester a b c d e h k := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.sylvester, quadCubicSylvester, Fin.addCases,
        Polynomial.coeff_monomial]
  rw [Polynomial.resultant, hM, det_quadCubicSylvester]

lemma reduced_resultant_eq_rawResB (b2 b4 b6 b8 : ℚ) :
    16 * (reducedNumPolyB b2 b4 b6 b8).resultant (dupDenPolyB b2 b4 b6) 2 3 =
      rawResB b2 b4 b6 b8 := by
  unfold reducedNumPolyB dupDenPolyB
  rw [resultant_quadratic_cubic]
  ring_nf

lemma resultant_B_eq_rawResB (b2 b4 b6 b8 : ℚ) :
    (dupNumPolyB b4 b6 b8).resultant (dupDenPolyB b2 b4 b6) 4 4 =
      rawResB b2 b4 b6 b8 := by
  let f := dupNumPolyB b4 b6 b8
  let g := dupDenPolyB b2 b4 b6
  let p := quotientPolyB b2
  let r := reducedNumPolyB b2 b4 b6 b8
  have hg3 : g.natDegree ≤ 3 := by
    dsimp [g, dupDenPolyB]
    compute_degree
  have hp1 : p.natDegree ≤ 1 := by
    dsimp [p, quotientPolyB]
    compute_degree
  have hpdeg : p.natDegree + 3 ≤ 4 := by omega
  have hr2 : r.natDegree ≤ 2 := by
    dsimp [r, reducedNumPolyB]
    compute_degree
  have hfgp : f + g * p = r := by
    dsimp [f, g, p, r, dupNumPolyB, dupDenPolyB, quotientPolyB, reducedNumPolyB]
    simp_rw [← Polynomial.monomial_zero_left]
    ring_nf
    rw [Polynomial.monomial_mul_monomial 3 1 (4 : ℚ) (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 3 0 (4 : ℚ) (b2 * (1 / 16))]
    rw [Polynomial.monomial_mul_monomial 2 1 b2 (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 2 0 b2 (b2 * (1 / 16))]
    rw [Polynomial.monomial_mul_monomial 1 1 (b4 * 2) (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 1 0 (b4 * 2) (b2 * (1 / 16))]
    rw [Polynomial.monomial_mul_monomial 0 1 b6 (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 0 0 b6 (b2 * (1 / 16))]
    ext n
    simp [Polynomial.coeff_monomial, Polynomial.coeff_C]
    split_ifs <;> ring_nf
  calc
    (dupNumPolyB b4 b6 b8).resultant (dupDenPolyB b2 b4 b6) 4 4 =
        f.resultant g 4 4 := rfl
    _ = f.coeff 4 ^ 1 * f.resultant g 4 3 := by
      simpa using
        (Polynomial.resultant_add_right_deg (f := f) (g := g) (m := 4) (n := 3)
          (k := 1) hg3)
    _ = f.resultant g 4 3 := by
      dsimp [f, dupNumPolyB]
      simp [Polynomial.coeff_monomial]
    _ = (f + g * p).resultant g 4 3 := by
      exact
        (Polynomial.resultant_add_mul_left (f := f) (g := g) (p := p) (m := 4) (n := 3)
          hpdeg hg3).symm
    _ = r.resultant g 4 3 := by
      rw [hfgp]
    _ = (-1 : ℚ) ^ (3 * 2) * g.coeff 3 ^ 2 * r.resultant g 2 3 := by
      simpa using
        (Polynomial.resultant_add_left_deg (f := r) (g := g) (m := 2) (n := 3)
          (k := 2) hr2)
    _ = 16 * r.resultant g 2 3 := by
      dsimp [g, dupDenPolyB]
      simp [Polynomial.coeff_monomial]
      norm_num
    _ = rawResB b2 b4 b6 b8 := by
      dsimp [r, g]
      exact reduced_resultant_eq_rawResB b2 b4 b6 b8

lemma rawResB_eq_delta_sq_of_b_relation
    (b2 b4 b6 b8 delta : ℚ)
    (hDelta : delta = -b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2 + 9 * b2 * b4 * b6)
    (hrel : b2 * b6 - b4 ^ 2 - 4 * b8 = 0) :
    rawResB b2 b4 b6 b8 = delta ^ 2 := by
  subst delta
  calc
    rawResB b2 b4 b6 b8 =
        (-b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2 + 9 * b2 * b4 * b6) ^ 2
          + 4 * rawResCofactor b2 b4 b6 b8 * (b2 * b6 - b4 ^ 2 - 4 * b8) := by
      ring_nf
    _ = (-b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2 + 9 * b2 * b4 * b6) ^ 2 := by
      rw [hrel]
      ring

theorem resultant_dupNum_dupDen (W : WeierstrassCurve ℚ) :
    (dupNumPoly W).resultant (dupDenPoly W) 4 4 = W.Δ ^ 2 := by
  have hspec :
      (dupNumPoly W).resultant (dupDenPoly W) 4 4 =
        rawResB W.b₂ W.b₄ W.b₆ W.b₈ := by
    simpa [dupNumPoly, dupDenPoly, dupNumPolyB, dupDenPolyB] using
      resultant_B_eq_rawResB W.b₂ W.b₄ W.b₆ W.b₈
  rw [hspec]
  have hrel : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
    rw [← W.b_relation]
    ring
  exact rawResB_eq_delta_sq_of_b_relation W.b₂ W.b₄ W.b₆ W.b₈ W.Δ rfl hrel

theorem resultant_dupNum_dupDen_ne_zero (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    (dupNumPoly W).resultant (dupDenPoly W) 4 4 ≠ 0 := by
  rw [resultant_dupNum_dupDen]
  exact pow_ne_zero 2 W.isUnit_Δ.ne_zero

structure DupBezoutAffine (W : WeierstrassCurve ℚ) where
  A : Polynomial ℚ
  B : Polynomial ℚ
  hAdeg : A.degree < (4 : WithBot ℕ)
  hBdeg : B.degree < (4 : WithBot ℕ)
  bezout :
    dupNumPoly W * A + dupDenPoly W * B = C (W.Δ ^ 2)

noncomputable def dup_bezout_affine (W : WeierstrassCurve ℚ) : DupBezoutAffine W :=
  Classical.choice <| by
    have hFdeg : (dupNumPoly W).natDegree ≤ 4 := by
      dsimp [dupNumPoly]
      compute_degree
    have hGdeg : (dupDenPoly W).natDegree ≤ 4 := by
      dsimp [dupDenPoly]
      compute_degree
      omega
    rcases Polynomial.exists_mul_add_mul_eq_C_resultant
        (dupNumPoly W) (dupDenPoly W) hFdeg hGdeg
        (Or.inl (by norm_num : (4 : ℕ) ≠ 0)) with
      ⟨A, B, hAdeg, hBdeg, hbez⟩
    rw [resultant_dupNum_dupDen] at hbez
    exact ⟨
      { A := A
        B := B
        hAdeg := hAdeg
        hBdeg := hBdeg
        bezout := hbez }⟩

noncomputable def naiveLogHeightP1Q (X Z : ℚ) : ℝ :=
  Real.log (max |(X : ℝ)| |(Z : ℝ)|)

private def dupNumHReal (W : WeierstrassCurve ℚ) (X Z : ℝ) : ℝ :=
  X ^ 4 - (W.b₄ : ℝ) * X ^ 2 * Z ^ 2
    - 2 * (W.b₆ : ℝ) * X * Z ^ 3 - (W.b₈ : ℝ) * Z ^ 4

private def dupDenHReal (W : WeierstrassCurve ℚ) (X Z : ℝ) : ℝ :=
  4 * X ^ 3 * Z + (W.b₂ : ℝ) * X ^ 2 * Z ^ 2
    + 2 * (W.b₄ : ℝ) * X * Z ^ 3 + (W.b₆ : ℝ) * Z ^ 4

private def dupHeightRawReal (W : WeierstrassCurve ℚ) (P : ℝ × ℝ) : ℝ :=
  max |dupNumHReal W P.1 P.2| |dupDenHReal W P.1 P.2|

private def p1SupUnit : Set (ℝ × ℝ) :=
  {P | max |P.1| |P.2| = 1}

private lemma ratCast_dupNumH (W : WeierstrassCurve ℚ) (X Z : ℚ) :
    ((dupNumH W X Z : ℚ) : ℝ) = dupNumHReal W (X : ℝ) (Z : ℝ) := by
  simp [dupNumH, dupNumHReal]

private lemma ratCast_dupDenH (W : WeierstrassCurve ℚ) (X Z : ℚ) :
    ((dupDenH W X Z : ℚ) : ℝ) = dupDenHReal W (X : ℝ) (Z : ℝ) := by
  simp [dupDenH, dupDenHReal]

private lemma continuous_dupHeightRawReal (W : WeierstrassCurve ℚ) :
    Continuous (dupHeightRawReal W) := by
  unfold dupHeightRawReal dupNumHReal dupDenHReal
  continuity

private lemma p1SupUnit_isCompact : IsCompact p1SupUnit := by
  let box : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hclosed : IsClosed p1SupUnit := by
    unfold p1SupUnit
    exact isClosed_eq
      ((continuous_fst.abs).max continuous_snd.abs)
      continuous_const
  have hsubset : p1SupUnit ⊆ box := by
    intro P hP
    change max |P.1| |P.2| = (1 : ℝ) at hP
    have hX : |P.1| ≤ (1 : ℝ) := by
      rw [← hP]
      exact le_max_left |P.1| |P.2|
    have hZ : |P.2| ≤ (1 : ℝ) := by
      rw [← hP]
      exact le_max_right |P.1| |P.2|
    exact ⟨abs_le.mp hX, abs_le.mp hZ⟩
  exact hbox.of_isClosed_subset hclosed hsubset

private lemma dupNumHReal_affine_eval
    (W : WeierstrassCurve ℚ) {X Z : ℝ} (hZ : Z ≠ 0) :
    dupNumHReal W X Z =
      Z ^ 4 * ((dupNumPoly W).map (algebraMap ℚ ℝ)).eval (X / Z) := by
  simp [dupNumHReal, dupNumPoly]
  field_simp [hZ]

private lemma dupDenHReal_affine_eval
    (W : WeierstrassCurve ℚ) {X Z : ℝ} (hZ : Z ≠ 0) :
    dupDenHReal W X Z =
      Z ^ 4 * ((dupDenPoly W).map (algebraMap ℚ ℝ)).eval (X / Z) := by
  simp [dupDenHReal, dupDenPoly]
  field_simp [hZ]

private lemma dupHeightRawReal_ne_zero_on_unit
    (W : WeierstrassCurve ℚ) [W.IsElliptic] {P : ℝ × ℝ}
    (hP : P ∈ p1SupUnit) :
    dupHeightRawReal W P ≠ 0 := by
  intro hheight
  have hmaxle : dupHeightRawReal W P ≤ 0 := by
    simp [hheight]
  have hFabs_le : |dupNumHReal W P.1 P.2| ≤ 0 := (max_le_iff.mp hmaxle).1
  have hGabs_le : |dupDenHReal W P.1 P.2| ≤ 0 := (max_le_iff.mp hmaxle).2
  have hF : dupNumHReal W P.1 P.2 = 0 :=
    abs_eq_zero.mp (le_antisymm hFabs_le (abs_nonneg _))
  have hG : dupDenHReal W P.1 P.2 = 0 :=
    abs_eq_zero.mp (le_antisymm hGabs_le (abs_nonneg _))
  by_cases hZ : P.2 = 0
  · have hXabs : |P.1| = (1 : ℝ) := by
      simpa [p1SupUnit, hZ] using hP
    have hXne : P.1 ≠ 0 := by
      intro hX
      norm_num [hX] at hXabs
    have hX4 : P.1 ^ 4 = 0 := by
      simpa [dupNumHReal, hZ] using hF
    exact (pow_ne_zero 4 hXne) hX4
  · let t : ℝ := P.1 / P.2
    have hF_eval :
        ((dupNumPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
      have hscale := dupNumHReal_affine_eval (W := W) (X := P.1) (Z := P.2) hZ
      have hmul : P.2 ^ 4 *
          ((dupNumPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
        simpa [t, hscale] using hF
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 4 hZ)
    have hG_eval :
        ((dupDenPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
      have hscale := dupDenHReal_affine_eval (W := W) (X := P.1) (Z := P.2) hZ
      have hmul : P.2 ^ 4 *
          ((dupDenPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
        simpa [t, hscale] using hG
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 4 hZ)
    let cert := dup_bezout_affine W
    have hbezR :
        ((dupNumPoly W).map (algebraMap ℚ ℝ)) * (cert.A.map (algebraMap ℚ ℝ))
          + ((dupDenPoly W).map (algebraMap ℚ ℝ)) * (cert.B.map (algebraMap ℚ ℝ))
            = Polynomial.C (((W.Δ ^ 2 : ℚ) : ℝ)) := by
      have hmap := congrArg (Polynomial.map (algebraMap ℚ ℝ)) cert.bezout
      simpa using hmap
    have hzeroDelta : (((W.Δ ^ 2 : ℚ) : ℝ)) = 0 := by
      have hEval := congrArg (fun p : Polynomial ℝ => p.eval t) hbezR
      simpa [hF_eval, hG_eval] using hEval.symm
    have hDelta_ne : (((W.Δ ^ 2 : ℚ) : ℝ)) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 W.isUnit_Δ.ne_zero)
    exact hDelta_ne hzeroDelta

private lemma dupHeightRawReal_pos_on_unit
    (W : WeierstrassCurve ℚ) [W.IsElliptic] {P : ℝ × ℝ}
    (hP : P ∈ p1SupUnit) :
    0 < dupHeightRawReal W P := by
  refine lt_of_le_of_ne ?_ ?_
  · exact le_trans (abs_nonneg _) (le_max_left _ _)
  · exact (dupHeightRawReal_ne_zero_on_unit (W := W) hP).symm

private lemma dupHeightRawReal_uniform_lower
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P ∈ p1SupUnit, δ ≤ dupHeightRawReal W P := by
  have hnonempty : p1SupUnit.Nonempty := by
    exact ⟨(1, 0), by norm_num [p1SupUnit]⟩
  obtain ⟨P₀, hP₀, hmin⟩ :=
    p1SupUnit_isCompact.exists_isMinOn hnonempty
      (continuous_dupHeightRawReal W).continuousOn
  exact ⟨dupHeightRawReal W P₀, dupHeightRawReal_pos_on_unit (W := W) hP₀,
    fun P hP => (isMinOn_iff.mp hmin) P hP⟩

private lemma dupNumHReal_scale
    (W : WeierstrassCurve ℚ) {M X Z : ℝ} (hM : M ≠ 0) :
    dupNumHReal W X Z =
      M ^ 4 * dupNumHReal W (X / M) (Z / M) := by
  simp [dupNumHReal]
  field_simp [hM]

private lemma dupDenHReal_scale
    (W : WeierstrassCurve ℚ) {M X Z : ℝ} (hM : M ≠ 0) :
    dupDenHReal W X Z =
      M ^ 4 * dupDenHReal W (X / M) (Z / M) := by
  simp [dupDenHReal]
  field_simp [hM]

private lemma dupHeightRawReal_scale
    (W : WeierstrassCurve ℚ) {M X Z : ℝ} (hMnonneg : 0 ≤ M) (hM : M ≠ 0) :
    dupHeightRawReal W (X, Z) =
      M ^ 4 * dupHeightRawReal W (X / M, Z / M) := by
  have hM4nonneg : 0 ≤ M ^ 4 := pow_nonneg hMnonneg 4
  rw [dupHeightRawReal, dupHeightRawReal,
    dupNumHReal_scale (W := W) (M := M) (X := X) (Z := Z) hM,
    dupDenHReal_scale (W := W) (M := M) (X := X) (Z := Z) hM]
  simp only [abs_mul]
  rw [abs_of_nonneg hM4nonneg, ← mul_max_of_nonneg _ _ hM4nonneg]

/--
Current raw `max |X| |Z|` height lower bound for the duplication binary forms.

The proof uses the affine Bezout certificate to rule out common zeros on the
real sup-unit boundary, extracts a positive minimum by compactness, and scales
back by homogeneity.
-/
theorem dup_projective_height_lower_height_api_seam
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∃ C0 : ℝ, ∀ X Z : ℚ, (X, Z) ≠ (0, 0) →
      naiveLogHeightP1Q (dupNumH W X Z) (dupDenH W X Z) ≥
        4 * naiveLogHeightP1Q X Z - C0 := by
  obtain ⟨δ, hδpos, hδlower⟩ := dupHeightRawReal_uniform_lower W
  refine ⟨-Real.log δ, ?_⟩
  intro X Z hXZ
  let x : ℝ := X
  let z : ℝ := Z
  let M : ℝ := max |x| |z|
  have hxz_ne : x ≠ 0 ∨ z ≠ 0 := by
    by_contra h
    push Not at h
    apply hXZ
    ext <;> exact_mod_cast (by simp [x, z] at h ⊢; tauto)
  have hMpos : 0 < M := by
    rcases hxz_ne with hx | hz
    · exact lt_of_lt_of_le (abs_pos.mpr hx) (le_max_left |x| |z|)
    · exact lt_of_lt_of_le (abs_pos.mpr hz) (le_max_right |x| |z|)
  have hMnonneg : 0 ≤ M := le_of_lt hMpos
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hunit : (x / M, z / M) ∈ p1SupUnit := by
    have hMabs : |M| = M := abs_of_nonneg hMnonneg
    simp [p1SupUnit, M, abs_div, hMabs, max_div_div_right hMnonneg, hMne]
  have hscale :
      dupHeightRawReal W (x, z) =
        M ^ 4 * dupHeightRawReal W (x / M, z / M) :=
    dupHeightRawReal_scale (W := W) hMnonneg hMne
  have hM4nonneg : 0 ≤ M ^ 4 := pow_nonneg hMnonneg 4
  have hraw_lower : M ^ 4 * δ ≤ dupHeightRawReal W (x, z) := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hδlower (x / M, z / M) hunit) hM4nonneg
  have hpos_lower : 0 < M ^ 4 * δ :=
    mul_pos (pow_pos hMpos 4) hδpos
  have hlog_lower :
      Real.log (M ^ 4 * δ) ≤ Real.log (dupHeightRawReal W (x, z)) :=
    Real.log_le_log hpos_lower hraw_lower
  have hheight_eq :
      naiveLogHeightP1Q (dupNumH W X Z) (dupDenH W X Z) =
        Real.log (dupHeightRawReal W (x, z)) := by
    simp [naiveLogHeightP1Q, dupHeightRawReal, x, z,
      ratCast_dupNumH, ratCast_dupDenH]
  have hbase_eq :
      naiveLogHeightP1Q X Z = Real.log M := by
    simp [naiveLogHeightP1Q, M, x, z]
  rw [hheight_eq, hbase_eq]
  calc
    Real.log (dupHeightRawReal W (x, z)) ≥ Real.log (M ^ 4 * δ) := hlog_lower
    _ = 4 * Real.log M + Real.log δ := by
      rw [Real.log_mul (pow_ne_zero 4 hMne) (ne_of_gt hδpos), Real.log_pow]
      norm_num
    _ = 4 * Real.log M - -Real.log δ := by
      ring

end

end WeierstrassCurve.HeightDoubling
