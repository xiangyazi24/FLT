# N13 fake 2-Kummer map: structural Lean route

## Status

The even-sextic infinity ambiguity is no longer a design obligation.  It is
proved in:

```text
FLT/Assumptions/MazurProof/N13InfinityHalf.lean
```

The production theorem is:

```lean
theorem N13InfinityHalf.two_nsmul_classOf_infinityHalf :
    2 • SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          N13InfinityHalf.infinityHalf =
      SexticMumford.classOf
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ)
        (SexticMumford.infinityMinusMumford
          (N13Mumford.model ℚ))
```

It is structural, not a finite search.  Put

```text
A = X^3 + 2 X^2 - X - 1
B = 2 X (X + 1)
u = X (X + 1)
v = -(2 X + 1)
g = Y - A.
```

`N13GaussianFactorization.f_eq_sum_squares` gives `f = A^2 + B^2`,
and the new module proves

```text
(u, Y-v)^2 = (g),       ord_{infinity+}(g) = -1.
```

The orientation of `(u,v,nInf=0)` is `-1`; hence its square has orientation
`-2`.  The principal oriented pair of `g` has orientation `-1`, and the
negative-infinity class contributes the other `-1`.  This is exactly the
displayed doubling identity.

The axiom audit for `halfIdeal_sq`, `halfFunction_plus_order`,
`mumfordRaw_infinityHalf_sq`, and
`two_nsmul_classOf_infinityHalf` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry` or
custom axiom.

## Existing API that should be reused

The relevant concrete types are:

```lean
abbrev M : SexticMumford.Model ℚ := N13Mumford.model ℚ
abbrev O : SexticMumford.InfinityOrder M :=
  N13Infinity.positiveInfinityOrder ℚ
abbrev G : Type :=
  SexticMumford.ConcretePic M O

abbrev L : Type :=
  N13SexticSquareclass.SexticAlgebra
-- definitionally: AdjoinRoot (N13Mumford.f ℚ)

abbrev T : Type :=
  Additive (FakeSquareClass.Target (algebraMap ℚ L))
```

The ideal/Picard layer is already present:

```lean
SexticMumford.mumfordIdeal
SexticMumford.mumfordIdealUnit
SexticMumford.mumfordIdeal_mul_conj_integral
SexticMumford.mumfordIdeal_mul_conj_fractional
SexticMumford.mumfordRaw
SexticMumford.classOf
SexticMumford.classOf_eq_iff
SexticMumford.principalOriented
```

The rank-two coordinate-ring API is also sufficient:

```lean
SexticMumford.coeff0
SexticMumford.coeffY
SexticMumford.recompose
SexticMumford.eq_iff_coeff
SexticMumford.conjugate
SexticMumford.norm
SexticMumford.norm_recompose
```

For clearing principal fractional-ideal relations, use:

```lean
SexticMumford.exists_integral_numerator_of_principal_relation
SexticMumford.exists_integral_factor_pair_of_principal_relation
FractionalIdeal.spanSingleton_eq_spanSingleton
```

The fake target already kills scalars and squares:

```lean
FakeSquareClass.scalar_eq_one
FakeSquareClass.square_eq_one
FakeSquareClass.eq_one_of_mul_sq_eq_scalar
FakeSquareClass.exists_units_and_class_eq_one
```

`N13CandidateCollapse.candidateClass_eq_one_of_dlog_eq_zero` already
collapses the four global candidate exponents using one residue-field
equation and the explicit square/scalar identity.  It does not enumerate
sixteen cases.

## First next module: the sextic field and `u(theta)`

The immediate next production module should be `N13MumfordKummerValue.lean`.
Its first theorem is irreducibility of the N13 sextic.  A reduction modulo
`3` certificate is the shortest route; over `F_3` the polynomial remains an
irreducible sextic.

Target declarations:

```lean
theorem f_irreducible :
    Irreducible (N13Mumford.f ℚ)

noncomputable instance f_irreducible_fact :
    Fact (Irreducible (N13Mumford.f ℚ)) :=
  ⟨f_irreducible⟩

noncomputable instance : Field L := inferInstance
```

For a balanced Mumford representative, define:

```lean
def uTheta (D : SexticMumford.Mumford M) : L :=
  AdjoinRoot.mk (N13Mumford.f ℚ) D.u

theorem uTheta_ne_zero (D : SexticMumford.Mumford M) :
    uTheta D ≠ 0 := by
  -- AdjoinRoot.mk_ne_zero_of_natDegree_lt
  -- D.u_monic.ne_zero and D.deg_u : D.u.natDegree ≤ 2
  -- N13Mumford.f_natDegree ℚ : degree 6

def uThetaUnit (D : SexticMumford.Mumford M) : Lˣ :=
  Units.mk0 (uTheta D) (uTheta_ne_zero D)

def mumfordFakeClass (D : SexticMumford.Mumford M) : T :=
  Additive.ofMul
    ((uThetaUnit D : Lˣ) :
      FakeSquareClass.Target (algebraMap ℚ L))
```

Also add this missing generic target lemma:

```lean
@[simp] theorem FakeSquareClass.target_sq_eq_one
    {K L : Type*} [CommRing K] [CommRing L]
    (e : K →+* L) (z : FakeSquareClass.Target e) :
    z ^ 2 = 1 := by
  refine QuotientGroup.induction_on z ?_
  intro x
  exact FakeSquareClass.square_eq_one e x
```

After type-tag conversion it gives `2 • x = 0` in `Additive (Target e)`,
so every double is automatically in the Kummer kernel.

## Well-definedness: use conjugation, not divisor enumeration

Do not prove well-definedness by running Cantor composition or by splitting
on possible Mumford degrees.

The algebraic core is the following fixed-unit lemma:

```lean
theorem fixed_coordinate_unit_is_scalar
    (epsilon : (N13Mumford.CoordinateRing ℚ)ˣ)
    (hfix :
      SexticMumford.conjugate M (epsilon : _) = epsilon) :
    ∃ q : ℚˣ,
      epsilon =
        Units.map
          (algebraMap ℚ (N13Mumford.CoordinateRing ℚ)).toMonoidHom q
```

Proof outline:

1. Apply `coeffY` to `hfix`.  Conjugation changes the sign of the `Y`
   coefficient, so characteristic zero gives `coeffY epsilon = 0`.
2. `recompose` makes `epsilon = xClass p`.
3. Apply the same argument to `epsilon⁻¹ = xClass r`.
4. From `epsilon * epsilon⁻¹ = 1`, injectivity of `xClass` gives
   `p*r=1` in `ℚ[X]`; hence both are constant.

For a principal relation among two or three Mumford ideals:

1. Clear the fractional multiplier using
   `SexticMumfordPrincipalNumerator`.
2. Conjugate the relation using
   `SexticMumfordIdealConjugation`.
3. Multiply the relation and its conjugate.
4. Replace each `I(u,v) * I(u,-v)` by `(u)` using
   `mumfordIdeal_mul_conj_fractional`.
5. Equality of principal fractional ideals differs by a coordinate-ring
   unit.  The unit is conjugation-fixed, hence scalar by the preceding
   lemma.
6. At `theta`, the norm of `p+qY` becomes `p(theta)^2`, since
   `f(theta)=0`.  Thus the remaining discrepancy is a square times a
   rational scalar.

The two exact interface theorems should be:

```lean
theorem mumfordFakeClass_eq_of_classOf_eq
    (D E : SexticMumford.Mumford M)
    (h : SexticMumford.classOf M O D =
      SexticMumford.classOf M O E) :
    mumfordFakeClass D = mumfordFakeClass E

theorem mumfordFakeClass_mul_of_class_add
    (D E F : SexticMumford.Mumford M)
    (h : SexticMumford.classOf M O F =
      SexticMumford.classOf M O D +
        SexticMumford.classOf M O E) :
    mumfordFakeClass F =
      mumfordFakeClass D + mumfordFakeClass E
```

The second statement is written additively because `T` is an `Additive`
type tag; underneath it is the usual multiplicative identity.

## The actual representation seam

`ConcretePic M O` is already an additive commutative group, but the
repository does not yet prove that every class has a balanced Mumford
representative.  `SexticMumford.NormalFormData` asks for existence *and
uniqueness*; Kummer construction needs only existence.

Use the strictly weaker package:

```lean
class MumfordRepresentativeData : Prop where
  classOf_surjective :
    Function.Surjective (SexticMumford.classOf M O)
```

Then choose a representative:

```lean
noncomputable def representative
    [MumfordRepresentativeData] (c : G) :
    SexticMumford.Mumford M :=
  Classical.choose
    (MumfordRepresentativeData.classOf_surjective c)

theorem classOf_representative
    [MumfordRepresentativeData] (c : G) :
    SexticMumford.classOf M O (representative c) = c :=
  (Classical.choose_spec
    (MumfordRepresentativeData.classOf_surjective c))
```

The preceding two well-definedness theorems then define:

```lean
noncomputable def fakeKummer
    [MumfordRepresentativeData] : G →+ T where
  toFun c := mumfordFakeClass (representative c)
  map_zero' := ...
  map_add' c d := ...
```

Proving `MumfordRepresentativeData` is a genuine missing geometric theorem.
It should be proved by Riemann--Roch/Mumford reduction, not introduced as an
axiom and not replaced by a finite list of N13 classes.

## Exact kernel and the even-sextic correction

For a monic even sextic the correct generic first statement is:

```lean
theorem fakeKummer_eq_zero_iff_double_or_infinity
    [MumfordRepresentativeData] (P : G) :
    fakeKummer P = 0 ↔
      (∃ Q : G, P = 2 • Q) ∨
      (∃ Q : G,
        P = 2 • Q +
          SexticMumford.classOf M O
            (SexticMumford.infinityMinusMumford M))
```

The reverse implication is immediate from `target_sq_eq_one` and the fact
that the infinity class has fake value `1`.

The forward implication is the genuine half-divisor theorem.  Starting
from

```text
u(theta) = q * s(theta)^2
```

choose the reduced polynomial representative of `s`, lift the congruence
`u - q*s^2` as a multiple of `f`, and construct the half Mumford ideal.
The parity of the pole at infinity produces exactly the two alternatives
above.  This should be one reusable even-sextic theorem; no degree-case
enumeration is needed.

For N13 the new production theorem eliminates the second alternative:

```lean
def infinityHalfClass : G :=
  SexticMumford.classOf M O N13InfinityHalf.infinityHalf

theorem fakeKummer_eq_zero_iff_double
    [MumfordRepresentativeData] (P : G) :
    fakeKummer P = 0 ↔ ∃ Q : G, P = 2 • Q := by
  rw [fakeKummer_eq_zero_iff_double_or_infinity]
  constructor
  · rintro (h | ⟨Q, hQ⟩)
    · exact h
    · refine ⟨Q + infinityHalfClass, ?_⟩
      rw [nsmul_add,
        N13InfinityHalf.two_nsmul_classOf_infinityHalf]
      exact hQ
  · exact Or.inl
```

Consequently, if the arithmetic candidate/local-image layer proves
`fakeKummer P = 0` for every `P`, the endpoint required by
`N13TwoAdicEndgame` is immediate:

```lean
theorem twoSurjective_of_fakeKummer_trivial
    [MumfordRepresentativeData]
    (htrivial : ∀ P : G, fakeKummer P = 0) :
    N13TwoAdicEndgame.TwoSurjective G :=
  fun P => (fakeKummer_eq_zero_iff_double P).mp (htrivial P)
```

## Remaining arithmetic bridge

`N13CandidateCollapse` intentionally leaves two semantic obligations:

1. every global Kummer class belongs to the four-generator candidate
   envelope;
2. the local Kummer image lies in the kernel of
   `N13LocalDlogTwo.candidateDlog`.

Those belong after the geometric Kummer map and exact-kernel theorem.  The
candidate collapse itself is already structural and should not be replaced
by a sixteen-row certificate.

## Recommended implementation order

1. `N13MumfordKummerValue.lean`: mod-3 irreducibility, field instance,
   `uThetaUnit`, `mumfordFakeClass`, `target_sq_eq_one`.
2. `SexticMumfordFixedUnit.lean`: conjugation-fixed coordinate-ring units
   are scalar.
3. `N13MumfordKummerRelation.lean`: the two-ideal and three-ideal
   square/scalar relations.
4. `SexticMumfordRepresentative.lean`: balanced-representative
   surjectivity.
5. `SexticEvenKummerKernel.lean`: the double-or-infinity half-divisor
   theorem.
6. `N13MumfordKummer.lean`: assemble the homomorphism and use
   `N13InfinityHalf.two_nsmul_classOf_infinityHalf` to obtain exact kernel
   `2G`.
7. Connect the global/local candidate envelope to
   `N13CandidateCollapse`, yielding
   `N13TwoAdicEndgame.TwoSurjective G`.
