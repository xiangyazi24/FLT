
═══ BRIDGE  Q20 →dm1  SUBMITTED ═══
     "A6-HEIGHT design R6 (about the DUPLICATION MAP's resultant + Bezout fo…"
     ↳ debug: task 27492c47

[ask-gpt Q20 dm1 tid=27492c47 +0s] dispatched, waiting for answer
[ask-gpt Q20 dm1 tid=27492c47 +90s] waiting (status=processing)
[ask-gpt Q20 dm1 tid=27492c47 +180s] waiting (status=processing)
[ask-gpt Q20 dm1 tid=27492c47 +270s] waiting (status=processing)
[ask-gpt Q20 dm1 tid=27492c47 +360s] waiting (status=processing)
[ask-gpt Q20 dm1 tid=27492c47 +450s] waiting (status=processing)
[ask-gpt Q20 dm1 tid=27492c47 +522s] terminal: status=completed

═══ BRIDGE  Q20 →dm1  ✅ COMPLETE (18.0KB, 8m42s) ═══
     "A6-HEIGHT design R6 (about the DUPLICATION MAP's resultant + Bezout fo…"
     ↳ debug: task 27492c47

I’ll first audit the resultant normalization, then separate the universal algebra certificate from the Bezout/homogenization and integer height-estimate layers.

The key new point is that the raw resultant only becomes Δ² after rewriting with W.b_relation; use exists_mul_add_mul_eq_C_resultant for the later Bezout certificates.

1. resultant_dupNum_dupDen
Do not ask Lean to expand the Sylvester determinant and the bᵢ definitions in one proof. Split it into:


a universal resultant computation in the variables b₂,b₄,b₆,b₈;


the elliptic invariant reduction using W.b_relation or by unfolding the bᵢ.


Mathlib’s Polynomial.resultant is literally the determinant of the Sylvester matrix, with explicit optional degree parameters, and it has resultant_map_map for specialization. It also has the exact Bezout theorem you need, Polynomial.exists_mul_add_mul_eq_C_resultant. Lean Community
Use explicit degree parameters 4 4, not the default natDegree, because the denominator is naturally homogenized to degree 4 even though its affine polynomial has degree 3.
leanimport Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrassimport Mathlib.RingTheory.Polynomial.Resultant.Basicopen Polynomialnamespace WeierstrassCurve.HeightDoublingnoncomputable sectionvariable {R : Type*} [CommRing R]def dupNumPoly (W : WeierstrassCurve R) : Polynomial R :=  X^4 - C W.b₄ * X^2 - C (2 * W.b₆) * X - C W.b₈def dupDenPoly (W : WeierstrassCurve R) : Polynomial R :=  C 4 * X^3 + C W.b₂ * X^2 + C (2 * W.b₄) * X + C W.b₆
For the universal computation, use MvPolynomial and native_decide once. This is cleaner than forcing ring_nf to normalize a symbolic 8×8 determinant at every use.
leannamespace DupResultantUniversalabbrev S := MvPolynomial (Fin 4) ℤdef B₂ : S := MvPolynomial.X 0def B₄ : S := MvPolynomial.X 1def B₆ : S := MvPolynomial.X 2def B₈ : S := MvPolynomial.X 3def F : Polynomial S :=  X^4 - C B₄ * X^2 - C (2 * B₆) * X - C B₈def G : Polynomial S :=  C 4 * X^3 + C B₂ * X^2 + C (2 * B₄) * X + C B₆def rawRes : S :=  B₂^4 * B₈^2  - 6 * B₂^3 * B₄ * B₆ * B₈  + 4 * B₂^3 * B₆^3  + 4 * B₂^2 * B₄^3 * B₈  - 3 * B₂^2 * B₄^2 * B₆^2  - 48 * B₂^2 * B₄ * B₈^2  + 6 * B₂^2 * B₆^2 * B₈  + 240 * B₂ * B₄^2 * B₆ * B₈  - 162 * B₂ * B₄ * B₆^3  + 192 * B₂ * B₆ * B₈^2  - 144 * B₄^4 * B₈  + 108 * B₄^3 * B₆^2  + 384 * B₄^2 * B₈^2  - 1296 * B₄ * B₆^2 * B₈  + 729 * B₆^4  - 256 * B₈^3/--Universal symbolic resultant.Use explicit Sylvester degrees `4 4`. Since `G` has zero `X^4` coefficient,this agrees with the usual `4,3` resultant because `F` is monic.-/lemma resultant_F_G_raw :    F.resultant G 4 4 = rawRes := by  native_decideend DupResultantUniversal
If native_decide is too slow in your checkout, replace the proof by this one-time determinant expansion:
leanset_option maxHeartbeats 2000000 inlemma resultant_F_G_raw_alt :    DupResultantUniversal.F.resultant DupResultantUniversal.G 4 4      = DupResultantUniversal.rawRes := by  simp [    DupResultantUniversal.F,    DupResultantUniversal.G,    DupResultantUniversal.rawRes,    Polynomial.resultant,    Polynomial.sylvester,    Matrix.det_fin_succ  ]  ring_nf
The final Weierstrass theorem should specialize the universal lemma and then use the invariant relation


$$4b_8=b_2b_6-b_4^2.$$


Mathlib’s Weierstrass file defines the invariants b₂,b₄,b₆,b₈,Δ; b_relation is the relation above, and [W.IsElliptic] is the nonsingular/discriminant-nonzero structure. Lean Community
leandef rawResB (b₂ b₄ b₆ b₈ : ℚ) : ℚ :=  b₂^4 * b₈^2  - 6 * b₂^3 * b₄ * b₆ * b₈  + 4 * b₂^3 * b₆^3  + 4 * b₂^2 * b₄^3 * b₈  - 3 * b₂^2 * b₄^2 * b₆^2  - 48 * b₂^2 * b₄ * b₈^2  + 6 * b₂^2 * b₆^2 * b₈  + 240 * b₂ * b₄^2 * b₆ * b₈  - 162 * b₂ * b₄ * b₆^3  + 192 * b₂ * b₆ * b₈^2  - 144 * b₄^4 * b₈  + 108 * b₄^3 * b₆^2  + 384 * b₄^2 * b₈^2  - 1296 * b₄ * b₆^2 * b₈  + 729 * b₆^4  - 256 * b₈^3def rawResCofactor (b₂ b₄ b₆ b₈ : ℚ) : ℚ :=  3 * b₂^2 * b₄ * b₈  + b₂^2 * b₆^2  - 20 * b₂ * b₄^2 * b₆  - 8 * b₂ * b₆ * b₈  + 16 * b₄^4  - 28 * b₄^2 * b₈  + 81 * b₄ * b₆^2  + 16 * b₈^2lemma rawResB_eq_delta_sq_of_b_relation    (b₂ b₄ b₆ b₈ Δ : ℚ)    (hΔ : Δ = -b₂^2 * b₈ - 8*b₄^3 - 27*b₆^2 + 9*b₂*b₄*b₆)    (hrel : b₂ * b₆ - b₄^2 - 4*b₈ = 0) :    rawResB b₂ b₄ b₆ b₈ = Δ^2 := by  subst Δ  linear_combination    (norm := ring_nf [rawResB, rawResCofactor])    4 * rawResCofactor b₂ b₄ b₆ b₈ * hrel
Now the actual theorem:
leantheorem resultant_dupNum_dupDen    (W : WeierstrassCurve ℚ) :    (dupNumPoly W).resultant (dupDenPoly W) 4 4 = W.Δ^2 := by  let φ : DupResultantUniversal.S →+* ℚ :=    MvPolynomial.aeval      (fun i : Fin 4 =>        match i with        | 0 => W.b₂        | 1 => W.b₄        | 2 => W.b₆        | 3 => W.b₈)  have hraw :=    congrArg φ DupResultantUniversal.resultant_F_G_raw  have hspec :      (dupNumPoly W).resultant (dupDenPoly W) 4 4        =      rawResB W.b₂ W.b₄ W.b₆ W.b₈ := by    simpa [      φ,      dupNumPoly,      dupDenPoly,      DupResultantUniversal.F,      DupResultantUniversal.G,      DupResultantUniversal.rawRes,      rawResB,      DupResultantUniversal.B₂,      DupResultantUniversal.B₄,      DupResultantUniversal.B₆,      DupResultantUniversal.B₈    ] using hraw  rw [hspec]  have hrel : W.b₂ * W.b₆ - W.b₄^2 - 4*W.b₈ = 0 := by    -- `W.b_relation` is usually `4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2`.    linarith [W.b_relation]  exact    rawResB_eq_delta_sq_of_b_relation      W.b₂ W.b₄ W.b₆ W.b₈ W.Δ      (by        -- If `Δ` unfolds under this name, this is:        -- `rfl`; otherwise:        ring_nf [WeierstrassCurve.Δ])      hrel
If the Δ proof line does not reduce by ring_nf [WeierstrassCurve.Δ], use the direct fully-unfolded finish instead:
lean  ring_nf [    rawResB,    WeierstrassCurve.Δ,    WeierstrassCurve.b₂,    WeierstrassCurve.b₄,    WeierstrassCurve.b₆,    WeierstrassCurve.b₈  ]
That second ending is slower but avoids dependence on the exact statement name/shape of W.b_relation.
For nonsingularity:
leantheorem resultant_dupNum_dupDen_ne_zero    (W : WeierstrassCurve ℚ) [W.IsElliptic] :    (dupNumPoly W).resultant (dupDenPoly W) 4 4 ≠ 0 := by  rw [resultant_dupNum_dupDen]  exact sq_ne_zero W.Δ_ne_zero
If the field is named differently in your checkout, replace W.Δ_ne_zero by the corresponding projection from [W.IsElliptic].

2. dup_bezout_XY
Use exists_mul_add_mul_eq_C_resultant twice:


in the affine chart Z = 1, for F(X,1), G(X,1);


in the affine chart X = 1, for the reciprocal forms F(1,Z), G(1,Z).


The theorem has the exact useful shape:
leanPolynomial.exists_mul_add_mul_eq_C_resultant  (f g : Polynomial R)  (hf : f.natDegree ≤ m)  (hg : g.natDegree ≤ n)  (H : m ≠ 0 ∨ n ≠ 0)
and returns p q with degree bounds and
leanf * p + g * q = C (f.resultant g m n)
as documented. Lean Community
First define homogeneous evaluation.
leandef homEval (d : ℕ) (p : Polynomial ℚ) (X Z : ℚ) : ℚ :=  ∑ i in Finset.range (d + 1), p.coeff i * X^i * Z^(d - i)def dupNumH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=  X^4 - W.b₄ * X^2 * Z^2 - 2 * W.b₆ * X * Z^3 - W.b₈ * Z^4def dupDenH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=  4 * X^3 * Z + W.b₂ * X^2 * Z^2    + 2 * W.b₄ * X * Z^3 + W.b₆ * Z^4lemma homEval_dupNumPoly    (W : WeierstrassCurve ℚ) (X Z : ℚ) :    homEval 4 (dupNumPoly W) X Z = dupNumH W X Z := by  simp [homEval, dupNumPoly, dupNumH]  ringlemma homEval_dupDenPoly    (W : WeierstrassCurve ℚ) (X Z : ℚ) :    homEval 4 (dupDenPoly W) X Z = dupDenH W X Z := by  simp [homEval, dupDenPoly, dupDenH]  ring
The reciprocal chart polynomials are:
leandef dupNumRevPoly (W : WeierstrassCurve ℚ) : Polynomial ℚ :=  C 1 - C W.b₄ * X^2 - C (2 * W.b₆) * X^3 - C W.b₈ * X^4def dupDenRevPoly (W : WeierstrassCurve ℚ) : Polynomial ℚ :=  C 4 * X + C W.b₂ * X^2 + C (2 * W.b₄) * X^3 + C W.b₆ * X^4lemma resultant_dupRev    (W : WeierstrassCurve ℚ) :    (dupNumRevPoly W).resultant (dupDenRevPoly W) 4 4 = W.Δ^2 := by  -- Same universal computation, or prove by specializing the same raw  -- resultant to the reversed polynomials.  -- The raw resultant is identical.  sorry
Now define binary cubic cofactors.
leanstructure BinaryCubicQ where  c0 : ℚ  c1 : ℚ  c2 : ℚ  c3 : ℚnamespace BinaryCubicQdef eval (A : BinaryCubicQ) (X Z : ℚ) : ℚ :=  A.c0 * Z^3 + A.c1 * X * Z^2 + A.c2 * X^2 * Z + A.c3 * X^3def ofPolynomialDegLT4 (p : Polynomial ℚ) : BinaryCubicQ :={ c0 := p.coeff 0  c1 := p.coeff 1  c2 := p.coeff 2  c3 := p.coeff 3 }lemma eval_ofPolynomialDegLT4    (p : Polynomial ℚ)    (hp : p.degree < (4 : WithBot ℕ))    (X Z : ℚ) :    (ofPolynomialDegLT4 p).eval X Z = homEval 3 p X Z := by  simp [ofPolynomialDegLT4, eval, homEval]  -- coefficients ≥ 4 vanish from `hp`  ringend BinaryCubicQ
The Z^7 Bezout identity:
leanstructure DupBezoutQ (W : WeierstrassCurve ℚ) where  R : ℚ  hR : R ≠ 0  AZ : BinaryCubicQ  BZ : BinaryCubicQ  AX : BinaryCubicQ  BX : BinaryCubicQ  bezoutZ :    ∀ X Z : ℚ,      R * Z^7 =        AZ.eval X Z * dupNumH W X Z          + BZ.eval X Z * dupDenH W X Z  bezoutX :    ∀ X Z : ℚ,      R * X^7 =        AX.eval X Z * dupNumH W X Z          + BX.eval X Z * dupDenH W X Z
Construction:
leantheorem dup_bezout_Q    (W : WeierstrassCurve ℚ) [W.IsElliptic] :    DupBezoutQ W := by  classical  have hFdeg : (dupNumPoly W).natDegree ≤ 4 := by    simp [dupNumPoly]  have hGdeg : (dupDenPoly W).natDegree ≤ 4 := by    simp [dupDenPoly]  rcases Polynomial.exists_mul_add_mul_eq_C_resultant      (dupNumPoly W) (dupDenPoly W)      hFdeg hGdeg (Or.inl (by norm_num : (4 : ℕ) ≠ 0))    with ⟨pZ, qZ, hpZdeg, hqZdeg, hBezZpoly⟩  have hFrevdeg : (dupNumRevPoly W).natDegree ≤ 4 := by    simp [dupNumRevPoly]  have hGrevdeg : (dupDenRevPoly W).natDegree ≤ 4 := by    simp [dupDenRevPoly]  rcases Polynomial.exists_mul_add_mul_eq_C_resultant      (dupNumRevPoly W) (dupDenRevPoly W)      hFrevdeg hGrevdeg (Or.inl (by norm_num : (4 : ℕ) ≠ 0))    with ⟨pX, qX, hpXdeg, hqXdeg, hBezXpoly⟩  refine  { R := W.Δ^2    hR := sq_ne_zero W.Δ_ne_zero    AZ := BinaryCubicQ.ofPolynomialDegLT4 pZ    BZ := BinaryCubicQ.ofPolynomialDegLT4 qZ    AX := BinaryCubicQ.ofPolynomialDegLT4 pX    BX := BinaryCubicQ.ofPolynomialDegLT4 qX    bezoutZ := ?_    bezoutX := ?_ }  · intro X Z    -- Homogenize `f*p + g*q = C Res`.    have hhom :=      congrArg (fun r : Polynomial ℚ => homEval 7 r X Z) hBezZpoly    -- Use:    -- homEval 7 (dupNumPoly*pZ) = dupNumH * homEval 3 pZ    -- homEval 7 (dupDenPoly*qZ) = dupDenH * homEval 3 qZ    -- homEval 7 (C (W.Δ^2)) = W.Δ^2 * Z^7    --    -- Then rewrite resultant to Δ².    rw [resultant_dupNum_dupDen] at hhom    simpa [      BinaryCubicQ.eval_ofPolynomialDegLT4,      homEval_dupNumPoly,      homEval_dupDenPoly,      homEval,      BinaryCubicQ.eval,      mul_add,      add_mul    ] using hhom.symm  · intro X Z    -- Homogenize the reciprocal-chart Bezout identity.    have hhom :=      congrArg (fun r : Polynomial ℚ => homEval 7 r Z X) hBezXpoly    -- After evaluating the reciprocal forms at `(Z,X)`,    -- they become the original homogeneous forms at `(X,Z)`.    have hrevF :        homEval 4 (dupNumRevPoly W) Z X = dupNumH W X Z := by      simp [homEval, dupNumRevPoly, dupNumH]      ring    have hrevG :        homEval 4 (dupDenRevPoly W) Z X = dupDenH W X Z := by      simp [homEval, dupDenRevPoly, dupDenH]      ring    rw [resultant_dupRev] at hhom    simpa [      hrevF,      hrevG,      BinaryCubicQ.eval_ofPolynomialDegLT4,      homEval,      BinaryCubicQ.eval,      mul_add,      add_mul    ] using hhom.symm
The two omitted homogenization simplifications are the only infrastructure lemmas you should add:
leanlemma homEval_mul    {p q : Polynomial ℚ} {d e : ℕ}    (hp : p.natDegree ≤ d)    (hq : q.natDegree ≤ e)    (X Z : ℚ) :    homEval (d + e) (p * q) X Z =      homEval d p X Z * homEval e q X Z := by  -- expand `homEval`, use coefficient convolution.  -- This is a reusable polynomial lemma.  sorrylemma homEval_C    (a : ℚ) (d : ℕ) (X Z : ℚ) :    homEval d (C a) X Z = a * Z^d := by  simp [homEval]
Use these inside dup_bezout_Q; they are better than relying on a giant simp.

3. Integer lower bound from Bezout identities
For the height lower bound, after clearing denominators, use integer versions of the forms. But the analytic inequality is easiest to state over ℚ first.
Define coefficient size:
leannamespace BinaryCubicQdef norm (A : BinaryCubicQ) : ℝ :=  |A.c0| + |A.c1| + |A.c2| + |A.c3|lemma abs_eval_le_norm_mul_height    (A : BinaryCubicQ) (X Z : ℤ) :    |(A.eval X Z : ℚ)| ≤      A.norm * (max (|X| : ℝ) (|Z| : ℝ))^3 := by  have hX : (|((X : ℚ))| : ℝ) ≤ max (|X| : ℝ) (|Z| : ℝ) := by    exact le_max_left _ _  have hZ : (|((Z : ℚ))| : ℝ) ≤ max (|X| : ℝ) (|Z| : ℝ) := by    exact le_max_right _ _  -- expand, apply triangle inequality and `mul_le_mul`  -- for each monomial.  simp [eval, norm]  nlinarith [    abs_nonneg (A.c0 : ℝ), abs_nonneg (A.c1 : ℝ),    abs_nonneg (A.c2 : ℝ), abs_nonneg (A.c3 : ℝ),    hX, hZ  ]end BinaryCubicQ
Now the main real-valued inequality:
leantheorem dup_eval_lower_Q    (W : WeierstrassCurve ℚ) [W.IsElliptic] :    ∃ K : ℝ, 0 < K ∧      ∀ X Z : ℤ,        (X, Z) ≠ (0, 0) →        let H : ℝ := max (|X| : ℝ) (|Z| : ℝ)        let V : ℝ :=          max            |(dupNumH W X Z : ℚ)|            |(dupDenH W X Z : ℚ)|        H^4 ≤ K * V := by  classical  let B := dup_bezout_Q W  let Cx : ℝ := B.AX.norm + B.BX.norm  let Cz : ℝ := B.AZ.norm + B.BZ.norm  let C : ℝ := max Cx Cz  have hC_nonneg : 0 ≤ C := by    dsimp [C, Cx, Cz]    positivity  refine ⟨C / |(B.R : ℝ)|, ?_, ?_⟩  · have hRpos : 0 < |(B.R : ℝ)| := abs_pos.mpr (by exact_mod_cast B.hR)    positivity  · intro X Z hXZ    let H : ℝ := max (|X| : ℝ) (|Z| : ℝ)    let V : ℝ :=      max |(dupNumH W X Z : ℚ)| |(dupDenH W X Z : ℚ)|    have hH_ge_one : 1 ≤ H := by      -- nonzero integer pair has max abs at least 1      dsimp [H]      by_cases hX0 : X = 0      · have hZ0 : Z ≠ 0 := by          intro hz          exact hXZ (by simp [hX0, hz])        have hzabs : (1 : ℝ) ≤ |Z| := by exact_mod_cast Int.one_le_abs hZ0        exact le_trans hzabs (le_max_right _ _)      · have hxabs : (1 : ℝ) ≤ |X| := by exact_mod_cast Int.one_le_abs hX0        exact le_trans hxabs (le_max_left _ _)    have hV_nonneg : 0 ≤ V := by      dsimp [V]      positivity    have hcoord : H = (|X| : ℝ) ∨ H = (|Z| : ℝ) := by      dsimp [H]      exact max_choice _ _    have hRpos : 0 < |(B.R : ℝ)| := abs_pos.mpr (by exact_mod_cast B.hR)    have hXineq :        |(B.R : ℝ)| * (|X| : ℝ)^7 ≤ C * H^3 * V := by      have hbez := B.bezoutX (X : ℚ) (Z : ℚ)      have h1 :=        BinaryCubicQ.abs_eval_le_norm_mul_height B.AX X Z      have h2 :=        BinaryCubicQ.abs_eval_le_norm_mul_height B.BX X Z      -- From `R*X^7 = AX*F + BX*G`      -- use abs triangle, each `|F|,|G| ≤ V`.      dsimp [V, H] at h1 h2 ⊢      have hFle : |(dupNumH W X Z : ℚ)| ≤ V := le_max_left _ _      have hGle : |(dupDenH W X Z : ℚ)| ≤ V := le_max_right _ _      -- This line is the intended close:      nlinarith [        abs_add ((B.AX.eval X Z : ℚ) * dupNumH W X Z)          ((B.BX.eval X Z : ℚ) * dupDenH W X Z),        abs_mul (B.AX.eval X Z : ℚ) (dupNumH W X Z),        abs_mul (B.BX.eval X Z : ℚ) (dupDenH W X Z),        h1, h2, hFle, hGle, le_max_left Cx Cz      ]    have hZineq :        |(B.R : ℝ)| * (|Z| : ℝ)^7 ≤ C * H^3 * V := by      have hbez := B.bezoutZ (X : ℚ) (Z : ℚ)      have h1 :=        BinaryCubicQ.abs_eval_le_norm_mul_height B.AZ X Z      have h2 :=        BinaryCubicQ.abs_eval_le_norm_mul_height B.BZ X Z      dsimp [V, H] at h1 h2 ⊢      have hFle : |(dupNumH W X Z : ℚ)| ≤ V := le_max_left _ _      have hGle : |(dupDenH W X Z : ℚ)| ≤ V := le_max_right _ _      nlinarith [        abs_add ((B.AZ.eval X Z : ℚ) * dupNumH W X Z)          ((B.BZ.eval X Z : ℚ) * dupDenH W X Z),        abs_mul (B.AZ.eval X Z : ℚ) (dupNumH W X Z),        abs_mul (B.BZ.eval X Z : ℚ) (dupDenH W X Z),        h1, h2, hFle, hGle, le_max_right Cx Cz      ]    have hmain :        |(B.R : ℝ)| * H^7 ≤ C * H^3 * V := by      rcases hcoord with hHX | hHZ      · simpa [hHX] using hXineq      · simpa [hHZ] using hZineq    have hH3pos : 0 < H^3 := by positivity    have hcancel :        |(B.R : ℝ)| * H^4 ≤ C * V := by      have hmul :          (|(B.R : ℝ)| * H^4) * H^3 ≤ (C * V) * H^3 := by        calc          (|(B.R : ℝ)| * H^4) * H^3              = |(B.R : ℝ)| * H^7 := by ring          _ ≤ C * H^3 * V := hmain          _ = (C * V) * H^3 := by ring      exact (mul_le_mul_right hH3pos).mp hmul    have hfinal : H^4 ≤ (C / |(B.R : ℝ)|) * V := by      nlinarith [hcancel, hRpos]    simpa [H, V]      using hfinal
That gives the pre-cancellation lower bound. To pass to reduced projective height, you need the standard bounded-cancellation lemma. The Bezout identities also give that.
After choosing an integer L > 0 clearing all rational coefficients in B.AX,B.BX,B.AZ,B.BZ,R and the forms, define integer forms dupNumHZ, dupDenHZ. Then:
leantheorem gcd_dup_eval_dvd_fixed    (W : WeierstrassCurve ℚ) [W.IsElliptic] :    ∃ N : ℤ, N ≠ 0 ∧      ∀ X Z : ℤ,        IsCoprime X Z →        Int.gcd          (dupNumHZ W X Z)          (dupDenHZ W X Z)          ∣ N := by  rcases dup_bezout_Q W with B  -- clear denominators in the two Bezout identities:  -- N * X^7 = AXZ * F + BXZ * G  -- N * Z^7 = AZZ * F + BZZ * G  --  -- If d = gcd(F,G), then d | N*X^7 and d | N*Z^7.  -- Since gcd(X,Z)=1, gcd(X^7,Z^7)=1, hence d | N.  sorry
The key arithmetic step is:
leanlemma dvd_of_dvd_mul_pow_pair    {d N X Z : ℤ}    (hcop : IsCoprime X Z)    (hX : d ∣ N * X^7)    (hZ : d ∣ N * Z^7) :    d ∣ N := by  -- use `hcop.pow_left.pow_right` or prove via prime factors;  -- over `ℤ`, route through `Int.gcd`.  sorry
Then the reduced height lower bound follows: reducing [F,G] by their gcd loses at most the fixed factor |N|.
leantheorem dup_projective_height_lower_from_bezout    (W : WeierstrassCurve ℚ) [W.IsElliptic] :    ∃ C : ℝ, ∀ X Z : ℤ,      IsCoprime X Z →      (X, Z) ≠ (0, 0) →      naiveLogHeightP1        (dupNumHZ W X Z)        (dupDenHZ W X Z)        ≥ 4 * naiveLogHeightP1 X Z - C := by  -- combine:  --   `dup_eval_lower_Q`  --   `gcd_dup_eval_dvd_fixed`  --   logarithms.  sorry
Practical recommendation
For piece 1, use the universal raw resultant + specialization pattern. It is far more reliable than trying to make the final theorem one massive ring_nf.
For piece 2, build the Bezout identities over ℚ first with exists_mul_add_mul_eq_C_resultant, homogenize them to get
leanR * Z^7 = AZ * F + BZ * GR * X^7 = AX * F + BX * G
then clear denominators only when you need the gcd/cancellation lemma. This keeps the algebraic identities clean and pushes integer bookkeeping to the final height layer.
