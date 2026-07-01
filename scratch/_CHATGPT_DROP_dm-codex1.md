# Q2776 (dm-codex1): implementing `E1CoverIntTwoAdicSurvivorsStatement`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local file: `FLT/Assumptions/MazurProof/N12E1FullCoverBridge.lean`  
Namespace: `MazurProof.RationalPointsN12`

## Recommendation

Use the Q2769 style: **`Fin M` residues plus Boolean arithmetic with `Int.ModEq`/`% M`**, not a `ZMod M` existential predicate.

Reason: for `M = 4, 8, 16`, the finite checker is just nested loops over `Fin M`, Boolean equality, and integer `%`/`==`; `native_decide` compiles it to small VM code. The `ZMod M` version is prettier mathematically, but it tends to pull in heavier `Fintype`, coercion, and ring-normalization paths. Keep `ZMod` out of the computational table unless you already have a checked Q2768 implementation.

The soundness proof should not prove facts by evaluating the finite table. It should only show that an actual integer primitive cover datum produces residues passing the `Fin M` predicate for `M=4,8,16`. Then the final proof uses `native_decide` only for the finite table.

## Code skeleton

```lean
import FLT.Assumptions.MazurProof.N12E1FullCoverBridge
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NativeDecide
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

namespace MazurProof.RationalPointsN12

/-- The S23 representatives. Keep this order stable for debugging `#eval`. -/
def S23List : List ℤ := [-6, -3, -2, -1, 1, 2, 3, 6]

/-- The eight two-adic survivors from the checked interface. -/
def twoAdicSurvivorBool (d0 d1 d3 : ℤ) : Bool :=
  (d0 == 1  && d1 == 1  && d3 == 1)  ||
  (d0 == 1  && d1 == -3 && d3 == -3) ||
  (d0 == -1 && d1 == -2 && d3 == 2)  ||
  (d0 == -1 && d1 == 6  && d3 == -6) ||
  (d0 == 3  && d1 == 2  && d3 == 6)  ||
  (d0 == 3  && d1 == -6 && d3 == -2) ||
  (d0 == -3 && d1 == -1 && d3 == 3)  ||
  (d0 == -3 && d1 == 3  && d3 == -1)

/-- Boolean mirror for `ProductSquareclassCondition` on S23 reps.
For signed squarefree S23 reps, product squareclass is trivial exactly when
the product is one of `1, 4, 9, 36`. -/
def productSquareclassBool (d0 d1 d3 : ℤ) : Bool :=
  let p := d0 * d1 * d3
  p == 1 || p == 4 || p == 9 || p == 36

/-- One residue, read as an integer in `[0,M)`. -/
abbrev resVal {M : ℕ} (x : Fin M) : ℤ := (x.val : ℤ)

/-- Congruence to zero modulo `M`, evaluated as a Bool. -/
def modZeroBool (M : ℕ) (z : ℤ) : Bool :=
  decide (z ≡ 0 [ZMOD (M : ℤ)])

/-- For two-adic primitive projective reduction, require at least one coordinate
odd. This is exactly unit modulo `2^e`, but much cheaper to compute. -/
def oddPrimitiveBool {M : ℕ} (A B C T : Fin M) : Bool :=
  decide (A.val % 2 = 1) || decide (B.val % 2 = 1) ||
  decide (C.val % 2 = 1) || decide (T.val % 2 = 1)

/-- The two cover equations modulo `M`, evaluated on finite residues. -/
def coverResidueBool (M : ℕ) (d0 d1 d3 : ℤ)
    (A B C T : Fin M) : Bool :=
  modZeroBool M
    (d0 * resVal A ^ 2 - d1 * resVal B ^ 2 - resVal T ^ 2) &&
  modZeroBool M
    (d3 * resVal C ^ 2 - d0 * resVal A ^ 2 - 3 * resVal T ^ 2)

/-- Local two-adic solubility modulo `M` with primitive projective condition. -/
def localSoluble2Bool (M : ℕ) (d0 d1 d3 : ℤ) : Bool :=
  (List.finRange M).any fun A =>
    (List.finRange M).any fun B =>
      (List.finRange M).any fun C =>
        (List.finRange M).any fun T =>
          oddPrimitiveBool A B C T && coverResidueBool M d0 d1 d3 A B C T

/-- A two-adic certificate: failure modulo one of `4,8,16`. -/
def twoAdicBadBool (d0 d1 d3 : ℤ) : Bool :=
  (! localSoluble2Bool 4 d0 d1 d3) ||
  (! localSoluble2Bool 8 d0 d1 d3) ||
  (! localSoluble2Bool 16 d0 d1 d3)

/-- The finite table check: every S23 product-squareclass triple is either one
of the eight two-adic survivors or has a two-adic certificate. -/
theorem twoAdicFiniteTable_check :
    S23List.all (fun d0 =>
      S23List.all (fun d1 =>
        S23List.all (fun d3 =>
          if productSquareclassBool d0 d1 d3 then
            twoAdicSurvivorBool d0 d1 d3 || twoAdicBadBool d0 d1 d3
          else
            true))) = true := by
  native_decide
```

If `native_decide` is slow, first try only modulus `16`:

```lean
def twoAdicBadBool (d0 d1 d3 : ℤ) : Bool :=
  ! localSoluble2Bool 16 d0 d1 d3
```

In practice, `16` is usually enough for this cover. Keeping `4` and `8` as fallbacks gives smaller counterexample checks during debugging.

## Boolean-to-Prop bridge for the 8 survivors

Use one small lemma to turn `twoAdicSurvivorBool = true` into the target disjunction.

```lean
theorem twoAdicSurvivorBool_true_iff {d0 d1 d3 : ℤ} :
    twoAdicSurvivorBool d0 d1 d3 = true ↔
      (d0 = 1  ∧ d1 = 1  ∧ d3 = 1)  ∨
      (d0 = 1  ∧ d1 = -3 ∧ d3 = -3) ∨
      (d0 = -1 ∧ d1 = -2 ∧ d3 = 2)  ∨
      (d0 = -1 ∧ d1 = 6  ∧ d3 = -6) ∨
      (d0 = 3  ∧ d1 = 2  ∧ d3 = 6)  ∨
      (d0 = 3  ∧ d1 = -6 ∧ d3 = -2) ∨
      (d0 = -3 ∧ d1 = -1 ∧ d3 = 3)  ∨
      (d0 = -3 ∧ d1 = 3  ∧ d3 = -1) := by
  unfold twoAdicSurvivorBool
  omega
```

If `omega` does not see through `==`, use:

```lean
  decide
```

or split by all comparisons using `by_cases d0 = ...` and close with `omega`. Since all constants are ground integers, this lemma is small.

## S23/product bridge

Do not unfold `InS23` in the final theorem. Prove one finite extractor.

```lean
theorem InS23.mem_S23List {d : ℤ} (h : InS23 d) : d ∈ S23List := by
  -- If `InS23` is a disjunction, this is:
  --   rcases h with rfl | rfl | ... <;> simp [S23List]
  -- If `InS23` is list membership, `simpa [S23List] using h`.
  native_decide

theorem ProductSquareclassCondition.to_bool {d0 d1 d3 : ℤ}
    (hd0 : InS23 d0) (hd1 : InS23 d1) (hd3 : InS23 d3)
    (hprod : ProductSquareclassCondition d0 d1 d3) :
    productSquareclassBool d0 d1 d3 = true := by
  -- Finite S23 proof. Avoid using semantic squareclass facts in the main proof.
  -- Case split the three `InS23` hypotheses and close by `native_decide`/`norm_num`.
  revert d0 d1 d3
  native_decide
```

If `native_decide` cannot reduce your local Prop definitions, replace these two bodies with explicit case splits over the eight S23 representatives. That is still only done once.

## Soundness: integer cover data gives finite local data

### Residue map into `Fin M`

```lean
/-- Integer reduced to the canonical residue in `Fin M`. -/
def intRes (M : ℕ) [NeZero M] (x : ℤ) : Fin M :=
  ⟨(x % (M : ℤ)).toNat, by
    have hMposN : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hMposZ : 0 < (M : ℤ) := by exact_mod_cast hMposN
    have hlt : x % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos x hMposZ
    have hnonneg : 0 ≤ x % (M : ℤ) := Int.emod_nonneg x (by exact_mod_cast (NeZero.ne M))
    omega⟩

@[simp] theorem intRes_val_modEq (M : ℕ) [NeZero M] (x : ℤ) :
    (intRes M x).val ≡ x [ZMOD (M : ℤ)] := by
  unfold intRes
  have hMposN : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMposZ : 0 < (M : ℤ) := by exact_mod_cast hMposN
  have hnonneg : 0 ≤ x % (M : ℤ) := Int.emod_nonneg x (by exact_mod_cast (NeZero.ne M))
  have htoNat : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) := Int.toNat_of_nonneg hnonneg
  simpa [Int.ModEq, htoNat] using (Int.mod_modEq x (M : ℤ)).symm
```

If `Int.toNat_of_nonneg` is not imported under that name, replace the last helper by a local theorem using `norm_num`/`omega`; the rest of the soundness API should stay unchanged.

### Cover equations reduce modulo `M`

```lean
theorem coverResidueBool_intRes
    {M : ℕ} [NeZero M]
    {d0 d1 d3 A B C T : ℤ}
    (hcover : CoverInt d0 d1 d3 A B C T) :
    coverResidueBool M d0 d1 d3
      (intRes M A) (intRes M B) (intRes M C) (intRes M T) = true := by
  rcases hcover with ⟨h1, h2⟩
  unfold coverResidueBool modZeroBool
  apply Bool.and_eq_true.mpr
  constructor
  · -- First equation modulo M.
    have hA := intRes_val_modEq M A
    have hB := intRes_val_modEq M B
    have hT := intRes_val_modEq M T
    have hleft :
        d0 * resVal (intRes M A) ^ 2 - d1 * resVal (intRes M B) ^ 2 -
          resVal (intRes M T) ^ 2 ≡
        d0 * A ^ 2 - d1 * B ^ 2 - T ^ 2 [ZMOD (M : ℤ)] := by
      gcongr
    have hzero : d0 * A ^ 2 - d1 * B ^ 2 - T ^ 2 = 0 := by
      nlinarith [h1]
    exact decide_eq_true (hleft.trans (by simp [hzero]))
  · -- Second equation modulo M.
    have hA := intRes_val_modEq M A
    have hC := intRes_val_modEq M C
    have hT := intRes_val_modEq M T
    have hleft :
        d3 * resVal (intRes M C) ^ 2 - d0 * resVal (intRes M A) ^ 2 -
          3 * resVal (intRes M T) ^ 2 ≡
        d3 * C ^ 2 - d0 * A ^ 2 - 3 * T ^ 2 [ZMOD (M : ℤ)] := by
      gcongr
    have hzero : d3 * C ^ 2 - d0 * A ^ 2 - 3 * T ^ 2 = 0 := by
      nlinarith [h2]
    exact decide_eq_true (hleft.trans (by simp [hzero]))
```

If `gcongr` does not handle `Int.ModEq.pow`, replace each `gcongr` block with explicit calls:

```lean
have hA2 := (Int.ModEq.pow 2 hA)
have hB2 := (Int.ModEq.pow 2 hB)
have hT2 := (Int.ModEq.pow 2 hT)
exact ((hA2.mul_left d0).sub (hB2.mul_left d1)).sub hT2
```

### Primitive integer data gives odd residue

This is the only primitive-projective pitfall. For `M=2^e`, primitive means not all integer coordinates are even, hence at least one finite residue is odd.

```lean
theorem two_dvd_of_intRes_even
    {M : ℕ} [NeZero M] (hM2 : (2 : ℕ) ∣ M)
    {x : ℤ}
    (hx : (intRes M x).val % 2 = 0) :
    (2 : ℤ) ∣ x := by
  have hres : ((intRes M x).val : ℤ) ≡ x [ZMOD (M : ℤ)] := intRes_val_modEq M x
  have h2M : (2 : ℤ) ∣ (M : ℤ) := by
    exact_mod_cast hM2
  have hres2 : ((intRes M x).val : ℤ) ≡ x [ZMOD (2 : ℤ)] :=
    hres.of_dvd h2M
  have hEvenRes : (2 : ℤ) ∣ ((intRes M x).val : ℤ) := by
    -- from `val % 2 = 0` over Nat
    exact_mod_cast (Nat.dvd_iff_mod_eq_zero.mpr hx)
  exact Int.modEq_zero_iff_dvd.mp ((hEvenRes.modEq_zero_int).symm.trans hres2)

theorem oddPrimitiveBool_intRes_of_PrimitiveInt4
    {M : ℕ} [NeZero M] (hM2 : (2 : ℕ) ∣ M)
    {A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T) :
    oddPrimitiveBool (intRes M A) (intRes M B) (intRes M C) (intRes M T) = true := by
  by_contra hfalse
  simp [oddPrimitiveBool, Bool.or_eq_true, decide_eq_true_eq] at hfalse
  have hA2 : (2 : ℤ) ∣ A := two_dvd_of_intRes_even hM2 hfalse.1
  have hB2 : (2 : ℤ) ∣ B := two_dvd_of_intRes_even hM2 hfalse.2.1
  have hC2 : (2 : ℤ) ∣ C := two_dvd_of_intRes_even hM2 hfalse.2.2.1
  have hT2 : (2 : ℤ) ∣ T := two_dvd_of_intRes_even hM2 hfalse.2.2.2
  -- Replace this accessor with the one your local `PrimitiveInt4` exposes.
  have hunit : IsUnit (2 : ℤ) := hprim.isUnit_of_dvd' hA2 hB2 hC2 hT2
  norm_num [Int.isUnit_iff] at hunit
```

If `PrimitiveInt4` is a Bezout tuple rather than a common-divisor API, first add a local helper mirroring `IsCoprime.isUnit_of_dvd'`:

```lean
theorem PrimitiveInt4.isUnit_of_dvd'
    {A B C T d : ℤ} (h : PrimitiveInt4 A B C T)
    (hA : d ∣ A) (hB : d ∣ B) (hC : d ∣ C) (hT : d ∣ T) : IsUnit d := by
  -- Use the local definition of `PrimitiveInt4` here once.
  -- Then keep all two-adic soundness code unchanged.
  ...
```

### Actual local-solubility soundness

```lean
theorem localSoluble2Bool_true_of_coverInt
    {M : ℕ} [NeZero M] (hM2 : (2 : ℕ) ∣ M)
    {d0 d1 d3 A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) :
    localSoluble2Bool M d0 d1 d3 = true := by
  unfold localSoluble2Bool
  -- The four witnesses are the canonical residues of the integer solution.
  -- `List.any_eq_true` / `List.mem_finRange` API names can vary; if needed,
  -- replace the next four lines by repeated `simp [List.any_eq_true]`.
  apply List.any_eq_true.mpr
  refine ⟨intRes M A, List.mem_finRange _, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨intRes M B, List.mem_finRange _, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨intRes M C, List.mem_finRange _, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨intRes M T, List.mem_finRange _, ?_⟩
  apply Bool.and_eq_true.mpr
  exact ⟨oddPrimitiveBool_intRes_of_PrimitiveInt4 hM2 hprim,
    coverResidueBool_intRes hcover⟩

theorem localSoluble2Bool_true_of_coverInt_4
    {d0 d1 d3 A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) :
    localSoluble2Bool 4 d0 d1 d3 = true :=
  localSoluble2Bool_true_of_coverInt (M := 4) (by norm_num) hprim hcover

theorem localSoluble2Bool_true_of_coverInt_8
    {d0 d1 d3 A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) :
    localSoluble2Bool 8 d0 d1 d3 = true :=
  localSoluble2Bool_true_of_coverInt (M := 8) (by norm_num) hprim hcover

theorem localSoluble2Bool_true_of_coverInt_16
    {d0 d1 d3 A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) :
    localSoluble2Bool 16 d0 d1 d3 = true :=
  localSoluble2Bool_true_of_coverInt (M := 16) (by norm_num) hprim hcover
```

## Prop-level finite table extractor

The computational table should feed a Prop theorem returning either an 8-survivor Bool or one of three failed local checks.

```lean
def twoAdicCertifiedBad (d0 d1 d3 : ℤ) : Prop :=
  localSoluble2Bool 4 d0 d1 d3 = false ∨
  localSoluble2Bool 8 d0 d1 d3 = false ∨
  localSoluble2Bool 16 d0 d1 d3 = false

theorem s23_product_twoAdic_survivor_or_bad
    {d0 d1 d3 : ℤ}
    (hd0 : InS23 d0) (hd1 : InS23 d1) (hd3 : InS23 d3)
    (hprod : ProductSquareclassCondition d0 d1 d3) :
    twoAdicSurvivorBool d0 d1 d3 = true ∨
      twoAdicCertifiedBad d0 d1 d3 := by
  -- Implementation strategy:
  -- 1. convert `InS23` to `d ∈ S23List`, or case-split directly;
  -- 2. convert `ProductSquareclassCondition` to `productSquareclassBool = true`;
  -- 3. close the finite cases with `native_decide`.
  --
  -- If the local Props are not reducible by `native_decide`, replace this body
  -- by explicit eight-way rcases on `hd0 hd1 hd3`; each ground goal closes by
  -- `native_decide` using `twoAdicFiniteTable_check`.
  revert d0 d1 d3
  native_decide
```

## Final theorem shape

Adjust the intro pattern to the exact current statement. The important structure is: derive three local-soluble facts from the actual cover, ask the finite table for survivor-or-bad, contradict any bad certificate, then convert survivor Bool to the eight disjunctions.

```lean
theorem e1CoverIntTwoAdicSurvivorsStatement_checked :
    E1CoverIntTwoAdicSurvivorsStatement := by
  intro d0 d1 d3 A B C T hd0 hd1 hd3 hprod hT hA hB hC hprim hcover

  have hloc4 : localSoluble2Bool 4 d0 d1 d3 = true :=
    localSoluble2Bool_true_of_coverInt_4 hprim hcover
  have hloc8 : localSoluble2Bool 8 d0 d1 d3 = true :=
    localSoluble2Bool_true_of_coverInt_8 hprim hcover
  have hloc16 : localSoluble2Bool 16 d0 d1 d3 = true :=
    localSoluble2Bool_true_of_coverInt_16 hprim hcover

  have hsurv_or_bad :=
    s23_product_twoAdic_survivor_or_bad hd0 hd1 hd3 hprod
  rcases hsurv_or_bad with hsurv | hbad
  · exact (twoAdicSurvivorBool_true_iff.mp hsurv)
  · exfalso
    rcases hbad with hbad4 | hbad8 | hbad16
    · rw [hloc4] at hbad4
      cases hbad4
    · rw [hloc8] at hbad8
      cases hbad8
    · rw [hloc16] at hbad16
      cases hbad16
```

If the target disjunction order differs from `twoAdicSurvivorBool_true_iff`, either reorder the Boolean lemma or finish the survivor branch with `tauto` after unpacking.

## Minimal final proof architecture

```text
Fin/Bool local checker
  ↓ native_decide finite table
s23_product_twoAdic_survivor_or_bad
  ↓ soundness from CoverInt + PrimitiveInt4 → localSoluble2Bool M = true
E1CoverIntTwoAdicSurvivorsStatement
```

This keeps the expensive part (`16^4` residue search over at most 512 triples) entirely computational and keeps the mathematical soundness small: integer equations reduce modulo `M`, and primitive integer data imply at least one odd residue for `M = 2^e`.
