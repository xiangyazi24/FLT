# Q2767 (dm-codex1): Lean route for `E1CoverIntSurvivingTriplesStatement`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local file from prompt: `FLT/Assumptions/MazurProof/N12E1FullCoverBridge.lean`  
Namespace: `MazurProof.RationalPointsN12`

Connector note: the local WIP file named in the prompt is not visible through the GitHub connector on `scratch`, so the route below is written against the definitions named in the prompt. It is intentionally modular: the finite checker/certificates can live downstream and only need small bridge lemmas from the existing WIP definitions.

## Executive route

Do **not** hand-prove 512 cases. Prove the theorem by a two-layer certificate architecture.

1. A finite decidable layer enumerates all triples `(d0,d1,d3)` in

```text
S23 = {±1, ±2, ±3, ±6}
```

satisfying `ProductSquareclassCondition d0 d1 d3`, and proves by `native_decide` that every non-survivor has either a real sign obstruction or a local obstruction modulo a small prime power.

2. A soundness layer proves that each certificate contradicts an actual primitive integer `CoverInt` datum.

The key local-modulus point is: use **prime powers only** for primitive projective checks. For modulus `p^e`, primitive integer data imply that at least one of `A,B,C,T` is a unit modulo `p^e`. This is false for a general composite modulus such as `6` or `12`, where different coordinates can be non-units at different primes. So use moduli like

```text
4, 8, 16, 3, 9, 5, 7, 13
```

and extend the list only if `#eval` shows a remaining non-survivor without a certificate.

## 1. Finite enumeration over S23 and product squareclass

Use a Boolean mirror of `InS23` and `ProductSquareclassCondition` for enumeration. Keep bridge lemmas from the existing Props to the Bool definitions.

```lean
import FLT.Assumptions.MazurProof.N12E1FullCoverBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NativeDecide
import Mathlib.Tactic.NormNum

namespace MazurProof.RationalPointsN12

/-- Representatives of the `{±1,±2,±3,±6}` squareclasses. -/
def S23List : List ℤ := [-6, -3, -2, -1, 1, 2, 3, 6]

/-- Boolean mirror of `InS23`; prove an iff to the local Prop once. -/
def inS23Bool (d : ℤ) : Bool :=
  d == -6 || d == -3 || d == -2 || d == -1 ||
  d == 1 || d == 2 || d == 3 || d == 6

/-- For squarefree signed representatives in `S23`, product squareclass is
represented by product equal to `1`, `4`, `9`, or `36`. -/
def productSquareclassBool (d0 d1 d3 : ℤ) : Bool :=
  let p := d0 * d1 * d3
  p == 1 || p == 4 || p == 9 || p == 36

/-- The four triples that are allowed to survive. -/
def survivorTripleBool (d0 d1 d3 : ℤ) : Bool :=
  (d0 == 3  && d1 == 2  && d3 == 6) ||
  (d0 == -1 && d1 == -2 && d3 == 2) ||
  (d0 == 1  && d1 == 1  && d3 == 1) ||
  (d0 == -3 && d1 == -1 && d3 == 3)

/-- Target bridge to your existing definition. Usually this is just
`unfold InS23 inS23Bool; omega` or `native_decide` after case splitting. -/
theorem inS23_iff_inS23Bool {d : ℤ} :
    InS23 d ↔ inS23Bool d = true := by
  -- If `InS23` is a disjunction over the eight representatives:
  --   unfold InS23 inS23Bool; omega
  -- If it is list-based:
  --   simp [InS23, inS23Bool, S23List]
  native_decide

/-- Target bridge to your existing product-squareclass condition. -/
theorem productSquareclass_iff_bool {d0 d1 d3 : ℤ} :
    ProductSquareclassCondition d0 d1 d3 ↔
      productSquareclassBool d0 d1 d3 = true := by
  -- Expected if `ProductSquareclassCondition` is squareclass-product on S23.
  -- Otherwise prove this by unfolding the local definition and normalizing the
  -- finite S23 representatives.
  native_decide
```

If either bridge is not definitionally decidable because the WIP definition is more semantic, replace the `native_decide` proof by one-time case splitting over `S23List`. Do not case split in the final theorem.

## 2. Real sign obstruction

From the two cover equations

```text
d0*A^2 - d1*B^2 = T^2,
d3*C^2 - d0*A^2 = 3*T^2,
```

and `A,B,C,T` nonzero, two immediate real obstructions are sound:

```text
d0 < 0 and 0 < d1     impossible by the first equation;
d3 < 0 and 0 < d0     impossible by the second equation.
```

Together with product squareclass sign, these kill all triples with `d3 < 0`.

```lean
/-- Sign-only obstruction. -/
def realBadBool (d0 d1 d3 : ℤ) : Bool :=
  (d0 < 0 && 0 < d1) || (d3 < 0 && 0 < d0)

/-- First real obstruction: LHS negative but RHS positive. -/
theorem cover_no_solution_of_d0_neg_d1_pos
    {d0 d1 d3 A B C T : ℤ}
    (hd0 : d0 < 0) (hd1 : 0 < d1)
    (hB : B ≠ 0) (hT : T ≠ 0)
    (hcover : CoverInt d0 d1 d3 A B C T) : False := by
  -- Extract `d0*A^2 - d1*B^2 = T^2` from `hcover`.
  -- Then `d0*A^2 ≤ 0`, `0 < d1*B^2`, so LHS < 0, while `0 < T^2`.
  rcases hcover with ⟨h1, h2⟩
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hTsq : 0 < T ^ 2 := sq_pos_of_ne_zero hT
  nlinarith

/-- Second real obstruction: LHS negative but RHS positive. -/
theorem cover_no_solution_of_d3_neg_d0_pos
    {d0 d1 d3 A B C T : ℤ}
    (hd3 : d3 < 0) (hd0 : 0 < d0)
    (hC : C ≠ 0) (hA : A ≠ 0) (hT : T ≠ 0)
    (hcover : CoverInt d0 d1 d3 A B C T) : False := by
  -- Extract `d3*C^2 - d0*A^2 = 3*T^2`.
  rcases hcover with ⟨h1, h2⟩
  have hCsq : 0 < C ^ 2 := sq_pos_of_ne_zero hC
  have hAsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hTsq : 0 < T ^ 2 := sq_pos_of_ne_zero hT
  nlinarith
```

If your `CoverInt` is not a pair of equations, replace the two `rcases hcover` lines by the accessor lemmas already used elsewhere.

## 3. Local obstruction checker over `ZMod q`

Define the local cover equations in `ZMod q`. The primitive residue predicate uses `ZMod.val` and `Nat.Coprime`. For prime powers this is the right finite predicate: one coordinate must be prime-to-`q`, i.e. a unit modulo `q`.

```lean
/-- At least one coordinate is a unit modulo `q`, expressed computationally by
coprimality of its canonical representative with `q`. Use this only for prime
power `q` in the integer soundness theorem. -/
def primitiveResidueMod (q : ℕ) [NeZero q]
    (A B C T : ZMod q) : Prop :=
  Nat.Coprime A.val q ∨ Nat.Coprime B.val q ∨
  Nat.Coprime C.val q ∨ Nat.Coprime T.val q

/-- Reduction of the two full-cover equations modulo `q`. -/
def coverResidueMod (q : ℕ) [NeZero q]
    (d0 d1 d3 : ℤ) (A B C T : ZMod q) : Prop :=
  ((d0 : ZMod q) * A ^ 2 - (d1 : ZMod q) * B ^ 2 = T ^ 2) ∧
  ((d3 : ZMod q) * C ^ 2 - (d0 : ZMod q) * A ^ 2 =
    (3 : ZMod q) * T ^ 2)

/-- Local solubility with primitive projective condition. -/
def localSolubleMod (q : ℕ) [NeZero q] (d0 d1 d3 : ℤ) : Prop :=
  ∃ A B C T : ZMod q,
    primitiveResidueMod q A B C T ∧
    coverResidueMod q d0 d1 d3 A B C T
```

Now each certificate is a tiny `native_decide` proof:

```lean
example : ¬ localSolubleMod 8 1 2 2 := by
  native_decide

example : ¬ localSolubleMod 3 2 1 2 := by
  native_decide
```

The examples above are placeholders showing the intended style; the actual theorem below lets Lean compute the needed certificates.

## 4. Automated certificate search

Use a fixed list of prime-power moduli. Avoid moduli with multiple prime factors unless you write a separate primitive-residue soundness lemma for each prime divisor.

```lean
/-- Moduli used for local certificates. All are prime powers. -/
def localCertBadBool (d0 d1 d3 : ℤ) : Bool :=
  decide (¬ localSolubleMod 4 d0 d1 d3) ||
  decide (¬ localSolubleMod 8 d0 d1 d3) ||
  decide (¬ localSolubleMod 16 d0 d1 d3) ||
  decide (¬ localSolubleMod 3 d0 d1 d3) ||
  decide (¬ localSolubleMod 9 d0 d1 d3) ||
  decide (¬ localSolubleMod 5 d0 d1 d3) ||
  decide (¬ localSolubleMod 7 d0 d1 d3) ||
  decide (¬ localSolubleMod 13 d0 d1 d3)

/-- A non-surviving product triple has either a real or local certificate. -/
def certifiedOrSurvivorBool (d0 d1 d3 : ℤ) : Bool :=
  if productSquareclassBool d0 d1 d3 then
    survivorTripleBool d0 d1 d3 || realBadBool d0 d1 d3 ||
      localCertBadBool d0 d1 d3
  else
    true

/-- The finite enumeration theorem. This is the only place where all S23 cases
are checked. If this fails, add a prime-power modulus to `localCertBadBool` and
rerun. -/
theorem finite_s23_certificate_check :
    S23List.all (fun d0 =>
      S23List.all (fun d1 =>
        S23List.all (fun d3 => certifiedOrSurvivorBool d0 d1 d3))) = true := by
  native_decide
```

This theorem is robust because it checks all `8^3` triples, but only activates certificates for triples satisfying the product condition. The four survivor triples are accepted without local obstruction.

For the final proof, you need a Prop-level extractor. It is usually easiest to produce a lemma with a finite case split over the three `InS23` hypotheses and close each ground case with `native_decide`.

```lean
/-- Prop-level statement extracted from the Boolean finite checker. -/
def certifiedBad (d0 d1 d3 : ℤ) : Prop :=
  realBadBool d0 d1 d3 = true ∨
  ¬ localSolubleMod 4 d0 d1 d3 ∨
  ¬ localSolubleMod 8 d0 d1 d3 ∨
  ¬ localSolubleMod 16 d0 d1 d3 ∨
  ¬ localSolubleMod 3 d0 d1 d3 ∨
  ¬ localSolubleMod 9 d0 d1 d3 ∨
  ¬ localSolubleMod 5 d0 d1 d3 ∨
  ¬ localSolubleMod 7 d0 d1 d3 ∨
  ¬ localSolubleMod 13 d0 d1 d3

/-- Finite case theorem used by the main proof. -/
theorem s23_product_survivor_or_certifiedBad
    {d0 d1 d3 : ℤ}
    (hd0 : InS23 d0) (hd1 : InS23 d1) (hd3 : InS23 d3)
    (hprod : ProductSquareclassCondition d0 d1 d3) :
    survivorTripleBool d0 d1 d3 = true ∨ certifiedBad d0 d1 d3 := by
  -- Recommended implementation:
  --   1. convert `hd0 hd1 hd3` using `inS23_iff_inS23Bool`;
  --   2. case split each into the eight representatives;
  --   3. use `productSquareclass_iff_bool` for `hprod`;
  --   4. close all ground goals with `native_decide`.
  -- This avoids a giant handwritten table.
  revert d0 d1 d3
  native_decide
```

If the final `native_decide` over arbitrary integers does not reduce because `InS23` is not computational, replace only the body by:

```lean
  have hd0b := (inS23_iff_inS23Bool.mp hd0)
  have hd1b := (inS23_iff_inS23Bool.mp hd1)
  have hd3b := (inS23_iff_inS23Bool.mp hd3)
  have hprodb := (productSquareclass_iff_bool.mp hprod)
  -- Then use a small local tactic/script to turn each Boolean membership into
  -- one of eight equalities and finish with `native_decide`.
```

## 5. Soundness of local certificates

For each prime-power modulus, an actual primitive integer solution gives a local solution.

The only delicate lemma is primitive reduction. State it once and prove it from your local `PrimitiveInt4` API.

```lean
/-- Primitive integer quadruple gives a primitive residue tuple modulo a prime
power. This is the main pitfall lemma: it is true for `q=p^e`, not for arbitrary
composite `q`. -/
theorem PrimitiveInt4.primitiveResidueMod_primePow
    {p e q : ℕ} [NeZero q]
    (hp : Nat.Prime p) (he : 0 < e) (hq : q = p ^ e)
    {A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T) :
    primitiveResidueMod q (A : ZMod q) (B : ZMod q) (C : ZMod q) (T : ZMod q) := by
  -- Proof route:
  -- If no coordinate is prime-to-q, then because `q=p^e`, `p` divides each
  -- coordinate. Use the common-divisor form of `PrimitiveInt4` to conclude
  -- `IsUnit (p:ℤ)`, contradicting primality.
  --
  -- Expected local helper if `PrimitiveInt4` is common-divisor based:
  --   hprim.isUnit_of_dvd' hpA hpB hpC hpT
  -- where `hpA : (p:ℤ) ∣ A`, etc.
  --
  -- If `PrimitiveInt4` is Bezout-based, first convert to the common-divisor
  -- criterion, mirroring the existing `IsCoprime.isUnit_of_dvd'` style.
  sorry

/-- Integer cover data reduce to local cover data modulo a prime power. -/
theorem localSolubleMod_of_int_cover_primePow
    {p e q : ℕ} [NeZero q]
    (hp : Nat.Prime p) (he : 0 < e) (hq : q = p ^ e)
    {d0 d1 d3 A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) :
    localSolubleMod q d0 d1 d3 := by
  refine ⟨(A : ZMod q), (B : ZMod q), (C : ZMod q), (T : ZMod q), ?_, ?_⟩
  · exact PrimitiveInt4.primitiveResidueMod_primePow hp he hq hprim
  · -- Cast the two integer equations in `CoverInt` to `ZMod q`.
    -- Usually:
    --   rcases hcover with ⟨h1, h2⟩
    --   constructor <;> norm_num [coverResidueMod, h1, h2]
    rcases hcover with ⟨h1, h2⟩
    constructor <;> simp [coverResidueMod, h1, h2]
```

Then package the eight moduli:

```lean
theorem local4_contradiction
    {d0 d1 d3 A B C T : ℤ}
    (hbad : ¬ localSolubleMod 4 d0 d1 d3)
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) : False := by
  exact hbad (localSolubleMod_of_int_cover_primePow
    (p := 2) (e := 2) (q := 4) (by norm_num) (by norm_num) (by norm_num)
    hprim hcover)

theorem local8_contradiction
    {d0 d1 d3 A B C T : ℤ}
    (hbad : ¬ localSolubleMod 8 d0 d1 d3)
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) : False := by
  exact hbad (localSolubleMod_of_int_cover_primePow
    (p := 2) (e := 3) (q := 8) (by norm_num) (by norm_num) (by norm_num)
    hprim hcover)

-- Similarly for 16 = 2^4, 3 = 3^1, 9 = 3^2, 5 = 5^1, 7 = 7^1, 13 = 13^1.
```

## 6. Soundness of a combined certificate

```lean
theorem certifiedBad_false_of_int_cover
    {d0 d1 d3 A B C T : ℤ}
    (hT : T ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T)
    (hcert : certifiedBad d0 d1 d3) : False := by
  rcases hcert with hreal | hloc4 | hloc8 | hloc16 | hloc3 | hloc9 | hloc5 | hloc7 | hloc13
  · -- unfold the two real sign branches and apply the appropriate real lemma.
    unfold realBadBool at hreal
    -- ground Boolean sign cases are all decidable; use `omega`/`norm_num` after
    -- destructing the Bool disjunction, or make `realBad` a Prop instead.
    native_decide
  · exact local4_contradiction hloc4 hprim hcover
  · exact local8_contradiction hloc8 hprim hcover
  · -- local16_contradiction hloc16 hprim hcover
    sorry
  · -- local3_contradiction hloc3 hprim hcover
    sorry
  · -- local9_contradiction hloc9 hprim hcover
    sorry
  · -- local5_contradiction hloc5 hprim hcover
    sorry
  · -- local7_contradiction hloc7 hprim hcover
    sorry
  · -- local13_contradiction hloc13 hprim hcover
    sorry
```

For production, define `certifiedBad` as an inductive certificate rather than a right-associated disjunction; then this proof is cleaner and has no ambiguity about which local contradiction to apply:

```lean
inductive E1LocalCert where
  | real
  | mod4 | mod8 | mod16 | mod3 | mod9 | mod5 | mod7 | mod13
  deriving DecidableEq, Repr

def certSound (cert : E1LocalCert) (d0 d1 d3 : ℤ) : Prop :=
  match cert with
  | .real => realBadBool d0 d1 d3 = true
  | .mod4 => ¬ localSolubleMod 4 d0 d1 d3
  | .mod8 => ¬ localSolubleMod 8 d0 d1 d3
  | .mod16 => ¬ localSolubleMod 16 d0 d1 d3
  | .mod3 => ¬ localSolubleMod 3 d0 d1 d3
  | .mod9 => ¬ localSolubleMod 9 d0 d1 d3
  | .mod5 => ¬ localSolubleMod 5 d0 d1 d3
  | .mod7 => ¬ localSolubleMod 7 d0 d1 d3
  | .mod13 => ¬ localSolubleMod 13 d0 d1 d3
```

Then the finite theorem can return `∃ cert, certSound cert d0 d1 d3`.

## 7. Final theorem assembly

The final proof is short once the finite certificate theorem and soundness lemmas exist.

```lean
theorem E1CoverIntSurvivingTriplesStatement_checked :
    E1CoverIntSurvivingTriplesStatement := by
  intro d0 d1 d3 A B C T hd0 hd1 hd3 hprod hT hA hB hC hprim hcover
  have hsurv_or_cert :=
    s23_product_survivor_or_certifiedBad hd0 hd1 hd3 hprod
  rcases hsurv_or_cert with hsurv | hcert
  · -- Convert `survivorTripleBool = true` into the required four-way disjunction.
    unfold survivorTripleBool at hsurv
    native_decide
  · exact False.elim
      (certifiedBad_false_of_int_cover hT hA hB hC hprim hcover hcert)
```

If the theorem target expects the disjunction exactly as

```text
(d0,d1,d3)=(3,2,6) ∨ ...
```

then use a small Boolean-to-Prop lemma:

```lean
theorem survivorTripleBool_eq_true_iff {d0 d1 d3 : ℤ} :
    survivorTripleBool d0 d1 d3 = true ↔
      (d0 = 3 ∧ d1 = 2 ∧ d3 = 6) ∨
      (d0 = -1 ∧ d1 = -2 ∧ d3 = 2) ∨
      (d0 = 1 ∧ d1 = 1 ∧ d3 = 1) ∨
      (d0 = -3 ∧ d1 = -1 ∧ d3 = 3) := by
  unfold survivorTripleBool
  omega
```

## 8. Pitfalls to avoid

1. **Do not use one projective primitive predicate modulo composite `q` with several primes.** Primitive integer data do not imply that some coordinate is a unit modulo `6` or `12`. Use prime powers.

2. **Do not use nonzero integer hypotheses as nonzero residue hypotheses.** A nonzero integer can reduce to `0` modulo `p`. The correct local residue condition comes from `PrimitiveInt4`, not from `A,B,C,T ≠ 0`.

3. **Do not manually maintain a giant obstruction table.** Let `native_decide` verify the finite table from `S23List`, `productSquareclassBool`, and `localSolubleMod`. The only hand-written mathematics should be soundness of real/local certificates.

4. **Use `ZMod` equations exactly matching `CoverInt`.** Keep the equations homogeneous:

```lean
(d0 : ZMod q) * A^2 - (d1 : ZMod q) * B^2 = T^2
(d3 : ZMod q) * C^2 - (d0 : ZMod q) * A^2 = (3 : ZMod q) * T^2
```

5. **Survivors are not claimed locally soluble by the checker.** The checker simply exempts the four triples because downstream AP/double-leg wrappers finish them.

## Recommended implementation order

1. Add `S23List`, `inS23Bool`, `productSquareclassBool`, `survivorTripleBool`.
2. Prove/adjust `inS23_iff_inS23Bool` and `productSquareclass_iff_bool`.
3. Add `coverResidueMod`, `primitiveResidueMod`, `localSolubleMod`.
4. Add `localCertBadBool` and prove `finite_s23_certificate_check` by `native_decide`.
5. Prove `PrimitiveInt4.primitiveResidueMod_primePow` once.
6. Prove `localSolubleMod_of_int_cover_primePow` and one contradiction lemma per modulus.
7. Prove `s23_product_survivor_or_certifiedBad` by finite case splitting/native decision.
8. Finish `E1CoverIntSurvivingTriplesStatement` by survivor-or-certificate.

This keeps the hard proof small: a primitive-mod-prime-power lemma plus finite computation, rather than dozens of manual congruence cases.
