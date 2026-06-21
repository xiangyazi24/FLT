# A6 R8 ADVERSARIAL AUDIT (FULL — Xiang's authoritative paste, 2026-06-21)

Verdict: the chain is mathematically sound ONLY IF the duplication/height part is fully
projective and integral. The hidden flaw to hunt is NOT in the abstract torsion argument.
It is in step (c): proving the LOWER height bound after cancellation. Prototype that first.

## 1. Exceptional cases audit
NEVER use an affine `x(2P) = dupNum(xP)/dupDen(xP)` as the primary statement — unsafe at torsion.
Use a projective xRep on PRIMITIVE integer reps:

    structure P1Q where
      X Z : ℤ
      prim : IsCoprime X Z
      not_both_zero : X ≠ 0 ∨ Z ≠ 0
    noncomputable def P1Q.logHeight (x : P1Q) : ℝ := Real.log (max x.X.natAbs x.Z.natAbs : ℝ)

Duplication stated PROJECTIVELY (P1Q.Same), covering: P=0 (xRep=[1:0]); 2P=0 (dupDen=0, output
[1:0]); affine denom zero (2-torsion, [F:0]→[1:0], cancellation can be huge so gcd-control must
cover G=0); x(P)=∞; dupNum=dupDen=0 impossible for primitive [X:Z] (resultant/discriminant ≠0).

## 2. Missing-lemma audit (risk flags)
A. xRep_two_nsmul_same_dup — project-specific, prove by cases on Affine.Point. RISK HIGH.
B. resultant(dupNum,dupDen)=Δ²≠0 — don't lean on bare Polynomial.resultant; EXPORT explicit
   Bezout certificates (DupBezoutCert: R≠0, bezout_X: Ux·F+Vx·G=R·X⁷, bezout_Z: Uz·F+Vz·G=R·Z⁷,
   coeff_bound deg-3). Exponent 7 = deg4 + Bezout deg3. A single Z=1 affine identity MISSES the
   infinity chart. RISK medium (explicit ring_nf certs) vs medium-high (abstract resultant).
C. Northcott.comp_of_finite_fibers — DOES NOT assume it's in Mathlib; full proof given:
     def Northcott (h:α→ℝ):Prop := ∀ B, {x | h x ≤ B}.Finite
     lemma comp_of_finite_fibers (f:α→β)(hβ:β→ℝ)(hN:Northcott hβ)
        (hfib:∀ y,{x|f x=y}.Finite): Northcott (fun x=>hβ(f x)) := by
       intro B; exact Set.Finite.subset ((hN B).biUnion fun y _=>hfib y) (by intro x hx; ...)
D. Base ℙ¹(ℚ) Northcott — NOT in Mathlib. Robust route: prove integer box first
     P1Q.mulHeight x := max X.natAbs Z.natAbs;  mulHeight_northcott_nat N : {x|mulHeight≤N}.Finite
     (X,Z∈[-N,N] primitive, not both zero); then logHeight_northcott via H≥1, log H≤B ⇒ H≤ceil(exp B).
E. logHeight is NOT scaling-invariant on RAW pairs — only after primitive normalization. Use
   P1Q.Same (x.X*y.Z = y.X*x.Z) + P1Q.logHeight_same, or always normalize raw pairs canonically.

## 3. Lower bound — where it works / breaks
[X:Z] primitive rep of x(P). H:=max|X||Z|, F:=dupNumZ, G:=dupDenZ, Hraw:=max|F||G|, g:=gcd|F||G|.
Projective height of [F:G] = log(Hraw/g). Upper: Hraw≤K·H⁴ (deg-4 forms). LOWER needs BOTH homog
Bezout identities R·X⁷=Ux·F+Vx·G, R·Z⁷=Uz·F+Vz·G (deg-3 coeffs) ⇒ |R|·H⁷≤K·H³·Hraw ⇒ Hraw≥(|R|/K)H⁴.
THEN cancellation: dup_gcd_dvd_resultant: gcd(|F|,|G|) ∣ |R| (common divisor divides R·X⁷ and R·Z⁷,
gcd(X,Z)=1 ⇒ divides R). MUST handle G=0: gcd(F,0)=|F|∣|R| — keeps [F:0]=[1:0] compatible.
Hout = Hraw/g ≥ const·H⁴/|R| ⇒ logHeight(x(2P)) ≥ 4·logHeight(x(P)) − C.
Target = dup_logHeight_lower_from_bezout (on P1Q.normalize output), NOT a bare resultant lemma.
5 ways it breaks: (1) affine F/G not homogeneous; (2) only ONE Bezout identity (misses ∞);
(3) ℚ-poly coeffs not cleared to ℤ (gcd is an INTEGER statement); (4) raw pair height treated as
projective ([F:0] primitive height = 0, NOT log|F|); (5) resultant=Δ² proven but cancellation never extracted.

## 4. Full A6 wiring (the blueprint)
    def xHeight E P := P1Q.logHeight (xRep E P)
    theorem xHeight_northcott : Northcott (xHeight E) :=
      Northcott.comp_of_finite_fibers (f:=xRep E)(hβ:=P1Q.logHeight) P1Q.logHeight_northcott (xRep_finite_fibers E)
    theorem rational_torsion_finite_from_xHeight E : Finite (AddCommGroup.torsion (E⧸ℚ).Point) := by
      rcases xHeight_double_lower E with ⟨C,hC0,hC⟩
      exact finite_torsion_of_northcott_double_lower (xHeight_northcott E) (fun P => hC P)
    theorem rational_torsion_finite_alias E : (AddCommGroup.torsion (E⧸ℚ).Point : Set _).Finite := by
      haveI := rational_torsion_finite_from_xHeight E; exact Set.toFinite _

## 5. Risk ranking (highest→lowest)
1. step(c) Bezout/resultant → LOWER bound (cancellation). PROTOTYPE FIRST, no elliptic points:
   dup_projective_height_lower_prototype : ∃C≥0, ∀ x:P1Q, logHeight(dupP1 E x) ≥ 4·logHeight x − C.
   If this works, the rest is bounded. If it fails: affine division slipped, ∞ chart missing, ℚ
   coeffs uncleared, or cancellation unbounded.
2. step(a) projective duplication formula (case splits around ∞, vertical tangent, Mathlib group law).
3. step(d) Northcott of xHeight (build logHeight_northcott + xRep_finite_fibers manually).
4. step(b) resultant/Bezout cert (explicit ring_nf certs SAFER than abstract Polynomial.resultant).
5. step(e) orbit-max torsion argument — LOW risk, abstract, uses AddCommGroup.torsion + Finset.max'.

## Honest verdict
Sound, does NOT need canonical height or Mordell-Weil, provided R2/R3 proven for a naive projective
x-height. No hidden deep theorem in the abstract argument or Northcott-on-x once ℙ¹(ℚ) Northcott is
available. The genuine danger: step(c) misstated — resultant=Δ²≠0 is NOT by itself the height lower
bound. Needed: primitive input + homogeneous Bezout + gcd divides fixed resultant ⇒ projective output
height ≥ 4·input − C. Prototype THAT exact lemma first.
