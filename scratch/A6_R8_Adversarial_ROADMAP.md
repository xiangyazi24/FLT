
═══ BRIDGE  Q22 →dm3  SUBMITTED ═══
     "A6-HEIGHT design R8 — ADVERSARIAL stress-test of the WHOLE A6 height-b…"
     ↳ debug: task 6b56b803

[ask-gpt Q22 dm3 tid=6b56b803 +0s] dispatched, waiting for answer
[ask-gpt Q22 dm3 tid=6b56b803 +90s] waiting (status=processing)
[ask-gpt Q22 dm3 tid=6b56b803 +180s] waiting (status=processing)
[ask-gpt Q22 dm3 tid=6b56b803 +270s] waiting (status=processing)
[ask-gpt Q22 dm3 tid=6b56b803 +360s] waiting (status=processing)
[ask-gpt Q22 dm3 tid=6b56b803 +389s] terminal: status=completed

═══ BRIDGE  Q22 →dm3  ✅ COMPLETE (15.9KB, 6m29s) ═══
     "A6-HEIGHT design R8 — ADVERSARIAL stress-test of the WHOLE A6 height-b…"
     ↳ debug: task 6b56b803

Verdict: the chain is mathematically sound **only if the duplication/height part is fully projective and integral**. The hidden flaw to hunt is not in the abstract torsion argument. It is in step (c): proving the **lower** height bound after cancellation. Prototype that first.

## 1. Exceptional cases audit

The chain must never use an affine expression like

```lean
x (2 • P) = dupNum (x P) / dupDen (x P)
```

as the primary statement. That form is unsafe at exactly the important torsion cases.

Use a projective `xRep`:

```lean
/-- Projective rational x-coordinate. Infinity is `[1 : 0]`. -/
structure P1Q where
  X Z : ℤ
  prim : IsCoprime X Z
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

/-- Logarithmic height on primitive projective representatives. -/
noncomputable def P1Q.logHeight (x : P1Q) : ℝ :=
  Real.log (max x.X.natAbs x.Z.natAbs : ℝ)
```

Then the duplication formula should be stated projectively:

```lean
def dupNumZ (E : WeierstrassCurve ℚ) : ℤ → ℤ → ℤ := sorry
def dupDenZ (E : WeierstrassCurve ℚ) : ℤ → ℤ → ℤ := sorry

/--
Safe duplication formula.

This must include:
* `P = 0`, where `xRep P = [1 : 0]`;
* `2 • P = 0`, where output is also `[1 : 0]`;
* affine points with denominator zero;
* ordinary affine points.
-/
theorem xRep_two_nsmul_same_dup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    P1Q.Same
      (xRep E (2 • P))
      ⟨dupNumZ E (xRep E P).X (xRep E P).Z,
       dupDenZ E (xRep E P).X (xRep E P).Z,
       by
         -- not both zero; follows from no common projective zero,
         -- ultimately from resultant/discriminant nonzero
         sorry⟩ := by
  sorry
```

The exceptional cases:

```text
P = 0:
  xRep(P) = [1:0].
  Homogeneous duplication must give [1:0].
  hX(P) = 0 and hX(2P) = 0.
  The lower bound requires C ≥ 0 or an equivalent enlarged constant.

2P = 0:
  affine denominator vanishes.
  Projectively, dupDen = 0 and dupNum ≠ 0.
  The output point is [1:0], whose primitive height is 0.
  You must not divide by dupDen.

P affine with dupDen = 0:
  same issue; this is 2-torsion.
  The raw pair `[F:0]` normalizes to `[1:0]`.
  The cancellation can be huge, so the gcd-control lemma must cover the case
  `G(X,Z) = 0`.

P with x(P)=∞:
  this is just the group identity/infinity point.
  `xRep = [1:0]`, and all height statements must include it.

dupNum = dupDen = 0:
  must be impossible for primitive `[X:Z]`.
  This is where the homogeneous resultant/discriminant nonzero statement is used.
```

The biggest possible div-by-zero slip is here:

```lean
-- Bad API: do not make this your main theorem.
theorem bad_affine_dup :
    xCoord (2 • P) = dupNumAffine (xCoord P) / dupDenAffine (xCoord P) := by
  -- breaks when `dupDenAffine = 0`
  sorry
```

The safe theorem is projective equality:

```lean
theorem good_projective_dup :
    P1Q.Same (xRep E (2 • P))
      (P1Q.ofRaw (dupNumZ E X Z) (dupDenZ E X Z) ?notBothZero) := by
  sorry
```

## 2. Missing lemma audit

Here is the dependency list with risk flags.

### A. `xRep_two_nsmul_same_dup`

Project-specific, not Mathlib. It must be proved by cases on `WeierstrassCurve.Affine.Point`.

```lean
theorem xRep_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    xRep E (0 : (E⁄ℚ).Point) = P1Q.infinity := by
  sorry

theorem xRep_two_nsmul_same_dup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    P1Q.Same (xRep E (2 • P))
      (P1Q.raw (dupNumZ E (xRep E P).X (xRep E P).Z)
               (dupDenZ E (xRep E P).X (xRep E P).Z)) := by
  sorry
```

Risk: high. The group-law formulas in Mathlib are available through the elliptic point API, but this exact duplication-coordinate theorem is yours.

### B. `resultant(dupNum, dupDen) = Δ² ≠ 0`

Do not rely too much on a high-level resultant API existing in exactly the form you want. Mathlib does have polynomial/resultant infrastructure, but the homogeneous integral certificate you need may not be packaged as “there exist Bezout polynomials with exactly the degree bounds needed for heights.” The safest route is to prove/export **explicit Bezout certificates** and only use the word “resultant” as a design explanation.

For height work, this is better than a bare resultant equality:

```lean
/--
Homogeneous Bezout certificate for the duplication forms.

The point is not just `resultant ≠ 0`; the height lower bound needs
identities controlling both coordinates.
-/
structure DupBezoutCert (E : WeierstrassCurve ℚ) where
  R : ℤ
  R_ne_zero : R ≠ 0

  Ux Vx Uz Vz : ℤ → ℤ → ℤ

  deg_bound_x : Prop
  deg_bound_z : Prop

  bezout_X :
    ∀ X Z : ℤ,
      Ux X Z * dupNumZ E X Z + Vx X Z * dupDenZ E X Z =
        R * X^7

  bezout_Z :
    ∀ X Z : ℤ,
      Uz X Z * dupNumZ E X Z + Vz X Z * dupDenZ E X Z =
        R * Z^7

  coeff_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ X Z : ℤ,
        |(Ux X Z : ℝ)| ≤ K * (max X.natAbs Z.natAbs : ℝ)^3 ∧
        |(Vx X Z : ℝ)| ≤ K * (max X.natAbs Z.natAbs : ℝ)^3 ∧
        |(Uz X Z : ℝ)| ≤ K * (max X.natAbs Z.natAbs : ℝ)^3 ∧
        |(Vz X Z : ℝ)| ≤ K * (max X.natAbs Z.natAbs : ℝ)^3
```

The exponent `7` is the expected `degree 4 + Bezout degree 3`. The exact exponent can be different depending on how you package the forms, but the proof must have the form:

```text
R * X^M = Ux * F + Vx * G
R * Z^M = Uz * F + Vz * G
```

A single affine identity only bounding `Z = 1` is not enough; it misses the infinity chart.

Risk: medium-high if using raw `Polynomial.resultant`; medium if using explicit certificates checked by `ring_nf`.

### C. Northcott composition via finite fibers

Do not assume a lemma named `Northcott.comp_of_finite_fibers` exists. It is easy to write.

```lean
def Northcott {α : Type*} (h : α → ℝ) : Prop :=
  ∀ B : ℝ, ({x : α | h x ≤ B} : Set α).Finite

lemma Northcott.comp_of_finite_fibers
    {α β : Type*}
    (f : α → β) (hβ : β → ℝ)
    (hN : Northcott hβ)
    (hfib : ∀ y : β, ({x : α | f x = y} : Set α).Finite) :
    Northcott (fun x : α => hβ (f x)) := by
  intro B
  let Sβ : Set β := {y | hβ y ≤ B}

  have hSβ : Sβ.Finite := hN B

  have hsub :
      ({x : α | hβ (f x) ≤ B} : Set α) ⊆
        ⋃ y ∈ Sβ, ({x : α | f x = y} : Set α) := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨f x, ?_⟩
    refine Set.mem_iUnion.mpr ?_
    exact ⟨hx, rfl⟩

  exact Set.Finite.subset
    (hSβ.biUnion fun y hy => hfib y)
    hsub
```

The exact `Set.Finite.biUnion` elaboration may need minor syntax adjustment, but the lemma is elementary. Mathlib’s torsion API exists under `AddCommGroup.torsion`/`AddCommGroup.mem_torsion`, and finite-orbit maximum arguments can use `Finset.max'`, `max'_mem`, and `max'_le_iff`. citeturn657878view0 citeturn740485view0

### D. Base `ℙ¹(ℚ)` Northcott

Do not assume this exact statement is in Mathlib:

```lean
theorem P1Q.logHeight_northcott :
    Northcott P1Q.logHeight := by
  sorry
```

It is elementary but has real-log annoyances. The most robust route is to prove a multiplicative/integer bound first.

```lean
def P1Q.mulHeight (x : P1Q) : ℕ :=
  max x.X.natAbs x.Z.natAbs

lemma P1Q.mulHeight_northcott_nat
    (N : ℕ) :
    ({x : P1Q | x.mulHeight ≤ N} : Set P1Q).Finite := by
  -- finite integer box:
  -- X,Z ∈ [-N,N], primitive, not both zero
  sorry

lemma P1Q.logHeight_northcott :
    Northcott P1Q.logHeight := by
  intro B
  -- `log H ≤ B` implies `H ≤ ceil(exp B)` since `H ≥ 1`.
  -- Then reduce to `mulHeight_northcott_nat`.
  sorry
```

The hidden API risk is around `Real.log`, `Real.exp`, `Nat.ceil`, and coercions. The number-theory content is not deep.

### E. `Height.logHeight_smul_eq_logHeight`

Do not assume this exists. More importantly, if you define height on raw pairs by

```lean
Real.log (max A.natAbs B.natAbs : ℝ)
```

then it is **not** scaling-invariant. Scaling invariance only holds after primitive normalization or after defining height on projective classes.

Use your own projective equivalence:

```lean
def P1Q.Same (x y : P1Q) : Prop :=
  x.X * y.Z = y.X * x.Z

theorem P1Q.logHeight_same
    {x y : P1Q}
    (hxy : P1Q.Same x y) :
    x.logHeight = y.logHeight := by
  -- because both reps are primitive, same rational projective point
  -- implies equality up to sign
  sorry
```

Or avoid proving full invariance by always normalizing raw pairs through one canonical function:

```lean
noncomputable def P1Q.normalize (A B : ℤ) (h : A ≠ 0 ∨ B ≠ 0) : P1Q := sorry

theorem P1Q.normalize_same
    (A B : ℤ) (h) :
    P1Q.Same (P1Q.normalize A B h) (P1Q.raw A B) := by
  sorry
```

## 3. Lower bound direction: where it works and where it can break

The lower bound is real, but only with both pieces:

```text
raw lower bound + bounded cancellation.
```

Let `[X:Z]` be a primitive integer representative of `x(P)` and define

```lean
let H  := max X.natAbs Z.natAbs
let F  := dupNumZ E X Z
let G  := dupDenZ E X Z
let Hraw := max F.natAbs G.natAbs
let g := Nat.gcd F.natAbs G.natAbs
```

The projective height of `[F:G]` is essentially

```text
log (Hraw / g).
```

The **upper bound** is easy:

```text
Hraw ≤ K * H^4
```

because `F` and `G` are degree-4 forms.

The **lower bound** needs homogeneous Bezout identities:

```text
R X^7 = Ux F + Vx G
R Z^7 = Uz F + Vz G
```

with `Ux,Vx,Uz,Vz` of degree `3`.

From these, if `H = max(|X|, |Z|)`, then either `H = |X|` or `H = |Z|`, and you get

```text
|R| * H^7 ≤ K * H^3 * Hraw
```

hence

```text
Hraw ≥ (|R| / K) * H^4
```

up to a harmless reciprocal constant.

Then you need cancellation control:

```lean
lemma dup_gcd_dvd_resultant
    (cert : DupBezoutCert E)
    {X Z : ℤ}
    (hprim : IsCoprime X Z) :
    Nat.gcd (dupNumZ E X Z).natAbs (dupDenZ E X Z).natAbs ∣ cert.R.natAbs := by
  -- any common divisor of F and G divides both
  -- `R * X^7` and `R * Z^7`;
  -- since gcd(X,Z)=1, it divides R.
  sorry
```

This must also handle `G = 0`. In that case

```text
gcd(F,0) = |F|,
```

so the lemma says `|F| ∣ |R|`. This is exactly what keeps the projective height of the 2-torsion output `[F:0] = [1:0]` compatible with the lower bound.

Finally:

```text
Hout = Hraw / gcd(F,G)
     ≥ const * H^4 / |R|.
```

Taking logs gives:

```text
logHeight(x(2P)) ≥ 4 * logHeight(x(P)) - C.
```

The Lean target should be this, not a bare resultant lemma:

```lean
theorem dup_logHeight_lower_from_bezout
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (cert : DupBezoutCert E) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : P1Q,
        P1Q.logHeight
          (P1Q.normalize
            (dupNumZ E x.X x.Z)
            (dupDenZ E x.X x.Z)
            (by
              -- no common zero
              sorry)) ≥
        4 * P1Q.logHeight x - C := by
  sorry
```

Then the group-level bound is a wrapper:

```lean
theorem xHeight_double_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ P : (E⁄ℚ).Point,
        xHeight E (2 • P) ≥ 4 * xHeight E P - C := by
  rcases dup_logHeight_lower_from_bezout E (dupBezoutCert E) with
    ⟨C, hCnonneg, hC⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro P
  have hdup := xRep_two_nsmul_same_dup E P
  -- rewrite `xHeight` through `xRep`, use `P1Q.logHeight_same`,
  -- then apply `hC (xRep E P)`.
  sorry
```

Where it can break:

```text
1. Using affine `F(x)/G(x)` instead of homogeneous `[F(X,Z):G(X,Z)]`.
2. Proving only one Bezout identity, e.g. `R = A(x)F(x)+B(x)G(x)`.
   That does not control the infinity chart.
3. Forgetting to clear denominators in the coefficients of `F,G`.
   GCD divisibility is an integer statement, not a ℚ-polynomial statement.
4. Treating raw pair height as projective height.
   `[F:0]` has primitive height 0, not `log |F|`.
5. Proving `resultant = Δ² ≠ 0` but never extracting the bounded-cancellation lemma.
```

## 4. Full A6 wiring

Once the height lemmas are available:

```lean
def xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point → ℝ :=
  fun P => P1Q.logHeight (xRep E P)

theorem xHeight_northcott
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Northcott (xHeight E) := by
  apply Northcott.comp_of_finite_fibers
    (f := xRep E)
    (hβ := P1Q.logHeight)
  · exact P1Q.logHeight_northcott
  · exact xRep_finite_fibers E

theorem rational_torsion_finite_from_xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) := by
  rcases xHeight_double_lower E with ⟨C, hCnonneg, hC⟩
  exact finite_torsion_of_northcott_double_lower
    (h := xHeight E)
    (C := C)
    (xHeight_northcott E)
    (by
      intro P
      -- match the orientation expected by the abstract lemma:
      -- either `h(2P) ≥ 4h(P)-C` or `4h(P)-C ≤ h(2P)`.
      exact hC P)
```

Then replace the Mordell-Weil-based alias:

```lean
theorem rational_torsion_finite_alias
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by
  classical
  haveI : Finite (AddCommGroup.torsion (E⁄ℚ).Point) :=
    rational_torsion_finite_from_xHeight E
  exact Set.toFinite _
```

The abstract torsion argument itself is safe: Mathlib has the additive torsion subgroup API, and finite maxima can be handled with `Finset.max'`/`max'_le_iff`. citeturn657878view0turn740485view0

## 5. Risk ranking

Highest to lowest risk:

### 1. Step (c): Bezout/resultant → **lower** height bound

This is the riskiest. The subtle part is cancellation. The prototype should not mention elliptic points at all:

```lean
theorem dup_projective_height_lower_prototype
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : P1Q,
        P1Q.logHeight
          (P1Q.normalize
            (dupNumZ E x.X x.Z)
            (dupDenZ E x.X x.Z)
            (dup_not_both_zero E x)) ≥
        4 * P1Q.logHeight x - C := by
  sorry
```

This is the single lemma to prototype first. If this works, the rest is bounded.

### 2. Step (a): projective duplication formula

The formula itself is standard, but Lean case splits around `∞`, tangent vertical, and the exact Mathlib group-law definitions may be annoying.

Target:

```lean
theorem xRep_two_nsmul_same_dup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    P1Q.Same (xRep E (2 • P))
      (P1Q.normalize
        (dupNumZ E (xRep E P).X (xRep E P).Z)
        (dupDenZ E (xRep E P).X (xRep E P).Z)
        (dup_not_both_zero E (xRep E P))) := by
  sorry
```

### 3. Step (d): Northcott of `xHeight`

This is not deep, but may require building `P1Q.logHeight_northcott` and finite fibers manually. The finite-fiber lemma is project-specific:

```lean
theorem xRep_finite_fibers
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : P1Q) :
    ({P : (E⁄ℚ).Point | xRep E P = x} : Set (E⁄ℚ).Point).Finite := by
  -- infinity fiber is singleton;
  -- affine fiber has at most two y-values.
  sorry
```

### 4. Step (b): resultant/Bezout certificate

If you try to use abstract `Polynomial.resultant`, this may become API-risky. If you use explicit certificates checked by `ring_nf`, it is much safer. It is algebraic grind, not a deep theorem.

### 5. Step (e): orbit-max torsion argument

Low risk. Already abstract and independent of elliptic curves. It uses only `AddCommGroup.torsion`, finite cyclic orbit/max, and Northcott. Mathlib has the torsion subgroup API. citeturn657878view0

## Honest verdict

The chain is sound and does **not** require canonical height or Mordell-Weil, provided R2/R3 are proved for a naive projective `x`-height. There is no hidden deep theorem in the abstract argument or Northcott-on-`x` once `ℙ¹(ℚ)` Northcott is available.

The genuine danger is that step (c) is often misstated. The statement

```text
resultant(dupNum, dupDen) = Δ² ≠ 0
```

is not by itself the height lower bound. The needed theorem is:

```text
primitive input + homogeneous Bezout + gcd divides fixed resultant
⇒ projective output height ≥ 4 input height − C.
```

Prototype this exact lemma first:

```lean
theorem dup_projective_height_lower_prototype
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : P1Q,
        P1Q.logHeight (dupP1 E x) ≥
          4 * P1Q.logHeight x - C := by
  sorry
```

If that lemma is proved, the A6-height route is a bounded project. If it fails, the likely reason is one of: affine division slipped in, infinity chart missing, rational coefficients not cleared, or cancellation was not bounded.

# ============ DE-RISK PLAN (from R8 adversarial) ============
# RISK is concentrated in the LOWER height bound after cancellation. The abstract argument + Northcott-on-x
# are sound (no hidden deep theorem) ONCE ℙ¹(ℚ) Northcott is available.
# PROTOTYPE FIRST (de-risk before committing): dup_projective_height_lower_prototype — a PURE binary-form /
#   resultant statement, NO elliptic points: for coprime binary quartic forms F,G with resultant R≠0, the
#   projective height of [F(X,Z):G(X,Z)] is ≥ 4·height[X:Z] − C. Needs: homogeneous Bezout (R·X⁷, R·Z⁷ — BOTH
#   charts incl. infinity, NOT just Z=1) + gcd(F(X,Z),G(X,Z)) ∣ R cancellation control.
# Also write the easy helper Northcott.comp_of_finite_fibers (R3 assumed it; may not be in Mathlib).
# IF the prototype works → the rest (EC dup formula R5, resultant=Δ² R6, base Northcott R7) is bounded → BUILD.
