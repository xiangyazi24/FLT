# Q183-dm1: division-polynomial coprimality for `xPair ≠ 0`

## Verdict

Mathlib currently has the division-polynomial definitions, recurrence lemmas, and coordinate-ring congruences, but it does **not** have a theorem saying

```lean
IsCoprime (W.Φ n) (W.ΨSq n)
```

or a root-level theorem saying that `Φₙ` and `ΨSqₙ` have no common root.  It also does not have an elliptic-divisibility-sequence coprimality theorem of the form `gcd(ψ_m, ψ_n) = ψ_gcd(m,n)`.

The cleanest **classical** proof is geometric:

```text
[Φₙ(x) : ΨSqₙ(x)] is the projective x-coordinate of [n]P.
Projective coordinates of a point are never [0:0].
```

But if this exact nonzero fact is needed *inside* the proof of the x-coordinate formula, then using the full formula would be circular.  In that case, the most Lean-realistic route is to prove `xPair_ne_zero` **simultaneously** with the `xRep_nsmul_same_xPair` induction, rather than as a standalone polynomial gcd theorem.

The standalone polynomial/EDS coprimality theorem is buildable in principle, but it is another substantial seam: it requires either the root-characterization of division polynomials or universal resultant formulas for division polynomials.

---

## Existing Mathlib API

Mathlib's division-polynomial file has:

```lean
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.Ψ₂Sq_eq
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ

WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd
WeierstrassCurve.ΨSq_even
WeierstrassCurve.ΨSq_odd
WeierstrassCurve.Φ_ofNat

WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_φ

WeierstrassCurve.map_ΨSq
WeierstrassCurve.map_Φ
WeierstrassCurve.baseChange_ΨSq
WeierstrassCurve.baseChange_Φ
```

The exact defining equation for `Φ` in Mathlib is:

```lean
-- definally, for `n : ℤ`
W.Φ n =
  Polynomial.X * W.ΨSq n
    - W.preΨ (n + 1) * W.preΨ (n - 1)
        * if Even n then 1 else W.Ψ₂Sq
```

The natural-number shifted theorem is:

```lean
-- theorem `WeierstrassCurve.Φ_ofNat`
W.Φ ((n : ℤ) + 1)
  = (Polynomial.X * W.preΨ' (n + 1) ^ 2
      * if Even n then 1 else W.Ψ₂Sq)
    - W.preΨ' (n + 2) * W.preΨ' n
      * if Even n then W.Ψ₂Sq else 1
```

The file `Mathlib.NumberTheory.EllipticDivisibilitySequence` has EDS definitions and recurrence lemmas such as:

```lean
preNormEDS'_even
preNormEDS'_odd
preNormEDS_even
preNormEDS_odd
normEDS_even
normEDS_odd
```

But its documentation still lists proving the expected divisibility/EDS properties of `normEDS` as TODO, and it does not expose EDS gcd/coprimality theorems.

So the gap is precise:

```text
present: definitions + recurrence equations + degree/map/baseChange/congruence lemmas
absent: division-polynomial root characterization, gcd/coprimality, resultant formulas
```

---

## Classical proof 1: geometric/basepoint-free proof

Let `K` be an algebraic closure of `k`, and let `x : K`.  Since `K` is algebraically closed, there exists `y : K` such that `(x,y)` lies on the Weierstrass curve.  If

```lean
(W.Φ n).eval x = 0
(W.ΨSq n).eval x = 0
```

then the pair `[Φₙ(x), ΨSqₙ(x)]` is `[0,0]`.  But the x-coordinate formula says:

```lean
SameP1
  ((n • Point.some x y h).xRep)
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

and `Point.xRep` is never zero.  Contradiction.

Lean shape:

```lean
namespace FLT.DivisionPolynomialCoprime

open Polynomial
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Projective pair used by the x-coordinate formula. -/
def xPair (n : ℤ) (x : K) : Fin 2 → K :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

/-- Algebraically closed fields have a point above every x-coordinate. -/
axiom exists_y_of_isAlgClosed
    [IsAlgClosed K]
    (x : K) :
    ∃ y : K, W.toAffine.Nonsingular x y

/-- SEAM2: x-coordinate formula. -/
axiom xRep_zsmul_same_xPair
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (n : ℤ) :
    SameP1
      ((n • (W.toAffine.Point.some x y h : W.toAffine.Point)).xRep)
      (xPair W n x)

/-- `xRep` is never the zero vector.  This is usually already available or one-line by cases. -/
axiom Point.xRep_ne_zero
    (P : W.toAffine.Point) :
    P.xRep ≠ ![(0 : K), 0]

/-- Projective equivalence to the zero vector is impossible from a nonzero vector. -/
lemma sameP1_ne_zero_right_of_left_ne_zero
    {v w : Fin 2 → K}
    (hvw : SameP1 v w)
    (hv : v ≠ ![(0 : K), 0]) :
    w ≠ ![(0 : K), 0] := by
  intro hw
  rcases hvw with ⟨u, hu⟩
  apply hv
  rw [hu, hw]
  ext i <;> fin_cases i <;> simp

/-- No common root over an algebraically closed field, assuming the x-coordinate formula. -/
theorem Φ_ΨSq_no_common_root_of_xcoord_formula
    [IsAlgClosed K]
    (n : ℤ) (x : K) :
    ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0) := by
  rintro ⟨hΦ, hΨ⟩
  rcases exists_y_of_isAlgClosed W x with ⟨y, hxy⟩
  have hsame := xRep_zsmul_same_xPair W hxy n
  have hright_ne : xPair W n x ≠ ![(0 : K), 0] :=
    sameP1_ne_zero_right_of_left_ne_zero hsame
      (Point.xRep_ne_zero
        (W := W)
        (n • (W.toAffine.Point.some x y hxy : W.toAffine.Point)))
  exact hright_ne (by
    ext i <;> fin_cases i <;> simp [xPair, hΦ, hΨ])

end FLT.DivisionPolynomialCoprime
```

This is the shortest proof if the x-coordinate formula is already available.  It is also the mathematically cleanest proof: it says `[Φₙ:ΨSqₙ]` is a morphism to `P¹`, so the representing pair is basepoint-free.

But this is not usable if `xPair_ne_zero` is needed to prove `xRep_zsmul_same_xPair` in the first place.

---

## Classical proof 2: relation + torsion/root characterization

This proof avoids directly using `xRep_nsmul_same_xPair`, but it still requires a root-characterization theorem for `ΨSq`:

```lean
(W.ΨSq n).eval x(P) = 0 ↔ n • P = 0.
```

That theorem is essentially a consequence of SEAM2, so this is only non-circular if you have a separate proof of the root-characterization.

The argument is:

1. Suppose `ΨSqₙ(x)=0` and `Φₙ(x)=0`.
2. Pick a point `P=(x,y)` over `x` in an algebraic closure.
3. From `ΨSqₙ(x)=0`, get `n • P = 0`.
4. From the defining relation for `Φₙ`, get a root of one of the neighboring division polynomials, or a root of the 2-division factor:

   ```text
   Φₙ = X ΨSqₙ - preΨₙ₊₁ preΨₙ₋₁ * (if Even n then 1 else Ψ₂Sq)
   ```

5. A root of `preΨ_{n+1}` or `preΨ_{n-1}` gives `(n+1) • P = 0` or `(n-1) • P = 0`, after converting to `ΨSq`.
6. Then `P=0` because `gcd(n,n±1)=1`, contradicting that `P` is affine.
7. In the odd case, a root of `Ψ₂Sq` gives `2 • P = 0`; since `gcd(n,2)=1`, again `P=0`.

Lean skeleton:

```lean
namespace FLT.DivisionPolynomialCoprime

open Polynomial
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Root-characterization seam for `ΨSq`. -/
axiom ΨSq_eval_eq_zero_iff_zsmul_eq_zero
    (m : ℤ)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    (W.ΨSq m).eval x = 0 ↔
      m • (W.toAffine.Point.some x y h : W.toAffine.Point) = 0

/-- A root of `preΨ m` is a root of `ΨSq m`. -/
lemma ΨSq_eval_zero_of_preΨ_eval_zero
    (m : ℤ) {x : K}
    (hpre : (W.preΨ m).eval x = 0) :
    (W.ΨSq m).eval x = 0 := by
  classical
  by_cases hm : Even m
  · rw [W.ΨSq_even m hm]
    simp [hpre]
  · -- Depending on local API, use `Int.not_even_iff_odd.mp hm`.
    have hodd : Odd m := by
      exact Int.not_even_iff_odd.mp hm
    rw [W.ΨSq_odd m hodd]
    simp [hpre]

/-- If consecutive multiples kill a point, the point is zero. -/
lemma eq_zero_of_zsmul_eq_zero_and_succ_zsmul_eq_zero
    {G : Type*} [AddCommGroup G]
    {n : ℤ} {P : G}
    (hn : n • P = 0)
    (hs : (n + 1) • P = 0) :
    P = 0 := by
  have h : ((n + 1) - n) • P = 0 := by
    calc
      ((n + 1) - n) • P = (n + 1) • P - n • P := by
        simp [sub_zsmul]
      _ = 0 := by simp [hn, hs]
  simpa using h

lemma eq_zero_of_zsmul_eq_zero_and_pred_zsmul_eq_zero
    {G : Type*} [AddCommGroup G]
    {n : ℤ} {P : G}
    (hn : n • P = 0)
    (hp : (n - 1) • P = 0) :
    P = 0 := by
  have h : (n - (n - 1)) • P = 0 := by
    calc
      (n - (n - 1)) • P = n • P - (n - 1) • P := by
        simp [sub_zsmul]
      _ = 0 := by simp [hn, hp]
  simpa using h

/-- Odd `n` killed together with `2` killed implies the point is zero. -/
lemma eq_zero_of_odd_zsmul_and_two_zsmul
    {G : Type*} [AddCommGroup G]
    {n : ℤ} {P : G}
    (hnodd : Odd n)
    (hn : n • P = 0)
    (h2 : (2 : ℤ) • P = 0) :
    P = 0 := by
  rcases hnodd with ⟨a, ha⟩
  -- `n = 2*a + 1`; hence `1 = n - a*2`.
  have h1 : (1 : ℤ) • P = 0 := by
    calc
      (1 : ℤ) • P = (n - a * 2) • P := by
        rw [ha]
        ring_nf
      _ = n • P - a • ((2 : ℤ) • P) := by
        simp [sub_zsmul, mul_zsmul]
      _ = 0 := by simp [hn, h2]
  simpa using h1

/-- Relation-based no-common-root theorem, assuming the `ΨSq` root-characterization. -/
theorem Φ_ΨSq_no_common_root_of_ΨSq_root_characterization
    (n : ℤ) (hn0 : n ≠ 0) (x : K) :
    ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0) := by
  classical
  rintro ⟨hΦ, hΨ⟩
  rcases exists_y_of_isAlgClosed W x with ⟨y, hxy⟩
  let P : W.toAffine.Point := W.toAffine.Point.some x y hxy

  have hnP : n • P = 0 :=
    (ΨSq_eval_eq_zero_iff_zsmul_eq_zero W n hxy).mp hΨ

  have hprod :
      ((W.preΨ (n + 1)).eval x) * ((W.preΨ (n - 1)).eval x)
        * (if Even n then (1 : K) else (W.Ψ₂Sq).eval x) = 0 := by
    have hdef :
        W.Φ n =
          Polynomial.X * W.ΨSq n
            - W.preΨ (n + 1) * W.preΨ (n - 1)
              * (if Even n then 1 else W.Ψ₂Sq) := by
      rfl
    have := congrArg (fun p : Polynomial K => p.eval x) hdef
    -- After evaluating and rewriting `hΦ` and `hΨ`, this is just arithmetic.
    -- Exact simp normal form may need `ring_nf`.
    simp [hΦ, hΨ] at this
    simpa [mul_assoc, mul_comm, mul_left_comm] using this

  by_cases hEven : Even n
  · simp [hEven] at hprod
    rcases mul_eq_zero.mp hprod with hplus | hminus
    · have hΨplus : (W.ΨSq (n + 1)).eval x = 0 :=
        ΨSq_eval_zero_of_preΨ_eval_zero W (n + 1) hplus
      have hplusP : (n + 1) • P = 0 :=
        (ΨSq_eval_eq_zero_iff_zsmul_eq_zero W (n + 1) hxy).mp hΨplus
      have hP0 : P = 0 :=
        eq_zero_of_zsmul_eq_zero_and_succ_zsmul_eq_zero hnP hplusP
      exact W.toAffine.some_ne_zero hxy hP0
    · have hΨminus : (W.ΨSq (n - 1)).eval x = 0 :=
        ΨSq_eval_zero_of_preΨ_eval_zero W (n - 1) hminus
      have hminusP : (n - 1) • P = 0 :=
        (ΨSq_eval_eq_zero_iff_zsmul_eq_zero W (n - 1) hxy).mp hΨminus
      have hP0 : P = 0 :=
        eq_zero_of_zsmul_eq_zero_and_pred_zsmul_eq_zero hnP hminusP
      exact W.toAffine.some_ne_zero hxy hP0

  · have hOdd : Odd n := Int.not_even_iff_odd.mp hEven
    simp [hEven] at hprod
    rcases mul_eq_zero.mp hprod with hleft | h2root
    · rcases mul_eq_zero.mp hleft with hplus | hminus
      · have hΨplus : (W.ΨSq (n + 1)).eval x = 0 :=
          ΨSq_eval_zero_of_preΨ_eval_zero W (n + 1) hplus
        have hplusP : (n + 1) • P = 0 :=
          (ΨSq_eval_eq_zero_iff_zsmul_eq_zero W (n + 1) hxy).mp hΨplus
        have hP0 : P = 0 :=
          eq_zero_of_zsmul_eq_zero_and_succ_zsmul_eq_zero hnP hplusP
        exact W.toAffine.some_ne_zero hxy hP0
      · have hΨminus : (W.ΨSq (n - 1)).eval x = 0 :=
          ΨSq_eval_zero_of_preΨ_eval_zero W (n - 1) hminus
        have hminusP : (n - 1) • P = 0 :=
          (ΨSq_eval_eq_zero_iff_zsmul_eq_zero W (n - 1) hxy).mp hΨminus
        have hP0 : P = 0 :=
          eq_zero_of_zsmul_eq_zero_and_pred_zsmul_eq_zero hnP hminusP
        exact W.toAffine.some_ne_zero hxy hP0
    · have hΨ2 : (W.ΨSq (2 : ℤ)).eval x = 0 := by
        simpa [WeierstrassCurve.ΨSq_two] using h2root
      have h2P : (2 : ℤ) • P = 0 :=
        (ΨSq_eval_eq_zero_iff_zsmul_eq_zero W (2 : ℤ) hxy).mp hΨ2
      have hP0 : P = 0 :=
        eq_zero_of_odd_zsmul_and_two_zsmul hOdd hnP h2P
      exact W.toAffine.some_ne_zero hxy hP0

end FLT.DivisionPolynomialCoprime
```

This proof is a good design target **after** the root-characterization is available.  It uses the actual Mathlib `Φ` definition and the `ΨSq_even`/`ΨSq_odd` decomposition.

Where `Δ ≠ 0` enters: it is used by `[W.IsElliptic]` to ensure the Weierstrass curve is smooth, so the affine point group is valid and affine points are not the identity.  In a pure resultant proof, the same hypothesis appears as nonvanishing of the discriminant factors in the resultants of relevant division polynomials.

---

## Classical proof 3: pure polynomial/EDS coprimality

A pure polynomial proof would prove these root-coprimality facts over an algebraic closure:

```lean
/-- Consecutive univariate division polynomials have no common root. -/
theorem preΨ_no_common_root_consecutive
    (m : ℤ) (x : K) :
    ¬ ((W.preΨ m).eval x = 0 ∧ (W.preΨ (m + 1)).eval x = 0)

/-- Odd-index roots are not 2-torsion roots. -/
theorem preΨ_no_common_root_Ψ₂Sq_of_odd
    {m : ℤ} (hm : Odd m) (x : K) :
    ¬ ((W.preΨ m).eval x = 0 ∧ W.Ψ₂Sq.eval x = 0)
```

Then the `Φ` relation gives `no_common_root Φ ΨSq` by parity splitting.

But proving `preΨ_no_common_root_consecutive` by induction on the EDS recurrence is not small.  The recurrence is nonlinear and has case splits in parity.  The invariant you actually need is essentially:

```lean
roots(preΨ_m) ∩ roots(preΨ_n) = roots(preΨ_gcd(m,n))
```

or a resultant theorem:

```lean
Resultant(preΨ_m, preΨ_n) = unit * Δ^A * integer-index-factors
```

for `gcd(m,n)=1`.  Mathlib does not currently have these facts for `preNormEDS` or for Weierstrass division polynomials.

So the pure EDS route is a real new development, not a quick induction.

---

## Recommended route for the keystone seam

### If `xRep_nsmul_same_xPair` is already proved

Use the geometric proof:

```lean
theorem xPair_ne_zero
    [IsAlgClosed K]
    (n : ℤ) (x : K) :
    xPair W n x ≠ ![(0 : K), 0] := by
  rcases exists_y_of_isAlgClosed W x with ⟨y, hxy⟩
  have hsame := xRep_zsmul_same_xPair W hxy n
  exact sameP1_ne_zero_right_of_left_ne_zero hsame
    (Point.xRep_ne_zero _)
```

This is the shortest and best path.

### If `xPair_ne_zero` is needed during the proof of `xRep_nsmul_same_xPair`

Do **not** try to prove a standalone global gcd theorem first.  Instead strengthen the induction theorem:

```lean
structure XCoordFormulaState
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) : Prop where
  same :
    SameP1
      ((n • (W.toAffine.Point.some x y h : W.toAffine.Point)).xRep)
      ![(W.Φ (n : ℤ)).eval x, (W.ΨSq (n : ℤ)).eval x]
  pair_ne_zero :
    ![(W.Φ (n : ℤ)).eval x, (W.ΨSq (n : ℤ)).eval x]
      ≠ ![(0 : K), 0]
```

In every induction step, after constructing `same`, derive `pair_ne_zero` from `same` and `Point.xRep_ne_zero`.  This avoids a separate division-polynomial gcd theorem entirely.

The step looks like:

```lean
have hsame_n :
    SameP1 ((n • P).xRep) (xPair W (n : ℤ) x) := ...

have hpair_ne_zero_n :
    xPair W (n : ℤ) x ≠ ![(0 : K), 0] :=
  sameP1_ne_zero_right_of_left_ne_zero hsame_n
    (Point.xRep_ne_zero (n • P))
```

This simultaneous-induction packaging is the best way to close the keystone if the only place you need coprimality is to make projective representatives legal.

---

## Exact theorem signatures to add

Root-level theorem over an algebraic closure:

```lean
theorem Φ_ΨSq_no_common_root
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℤ) (x : K) :
    ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)
```

Projective pair theorem:

```lean
theorem xPair_ne_zero
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℤ) (x : K) :
    ![(W.Φ n).eval x, (W.ΨSq n).eval x] ≠ ![(0 : K), 0]
```

Polynomial coprimality theorem over a field, if you really want it:

```lean
theorem IsCoprime_Φ_ΨSq
    {k : Type*} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℤ) :
    IsCoprime (W.Φ n) (W.ΨSq n)
```

This last theorem is slightly more work than the root-level theorem because you must move to an algebraic closure and use a polynomial lemma equating coprimality over `k[X]` with no common roots over an algebraic closure.  Mathlib has many of the building blocks around `Polynomial.IsRoot`, `Polynomial.Splits`, and `IsCoprime`, but the exact wrapper may need to be added locally.

Suggested local wrapper:

```lean
lemma Polynomial.isCoprime_of_no_common_root_algClosure
    {k : Type*} [Field k]
    {f g : Polynomial k}
    (h : ∀ x : AlgebraicClosure k,
      (Polynomial.map (algebraMap k (AlgebraicClosure k)) f).eval x = 0 →
      (Polynomial.map (algebraMap k (AlgebraicClosure k)) g).eval x ≠ 0) :
    IsCoprime f g := by
  -- prove by contradiction using a nonconstant common divisor and the fact that
  -- every nonconstant polynomial over `AlgebraicClosure k` has a root.
  sorry
```

---

## Final recommendation

For the current keystone, do **not** open a new EDS-coprimality project unless absolutely necessary.

Use this order of preference:

1. **Best**: prove `xPair_ne_zero` simultaneously with `xRep_nsmul_same_xPair`, deriving nonzero from `SameP1` and `Point.xRep_ne_zero` at each index.
2. **Second best**: if SEAM2 is already available, prove `xPair_ne_zero` immediately from SEAM2 over an algebraic closure.
3. **Only if needed later**: prove a standalone `Φ_ΨSq_no_common_root` via the `ΨSq` root-characterization and the defining relation for `Φ`.
4. **Avoid for now**: pure EDS/resultant coprimality.  Mathlib does not have the needed coprimality/resultant infrastructure for division polynomials yet.
