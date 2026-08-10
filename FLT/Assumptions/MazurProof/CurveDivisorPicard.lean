import FLT.Assumptions.MazurProof.CurveZetaEffectiveDivisors

/-!
# Divisor classes from graded closed points

The zeta-function layer already constructs effective divisors as finite
nonnegative combinations of closed points.  Picard geometry needs the signed
group completion: integer divisors, their degree, and the quotient by actual
principal divisors.

This file supplies that algebraic layer without postulating Riemann--Roch or a
class number.  A concrete curve must still construct its principal-divisor
subgroup and prove that its elements have degree zero.  Once that is done,
degree descends to the quotient, `Pic^n` is an honest fibre of the descended
degree map, and translation and canonical residual duality become additive
group calculations.
-/

namespace MazurProof.CurveZetaEffectiveDivisors

namespace ClosedPointGrading

variable (C : ClosedPointGrading)

/-! ## Signed divisors and degree -/

/-- A signed divisor is a finite integer combination of graded closed
points.  This is the group completion of the existing effective-divisor
monoid on the same atoms. -/
abbrev Divisor := C.Atom →₀ ℤ

/-- The integer degree of a signed divisor is the sum of each multiplicity
times the residue degree of its closed point. -/
def divisorDegree : C.Divisor →+ ℤ where
  toFun D := D.sum fun x m => m * (C.atomDegree x : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    exact Finsupp.sum_add_index' (by simp) (by
      intro x a b
      simp only [add_mul])

/-- Regard an effective divisor as a signed divisor by casting each
nonnegative multiplicity to an integer. -/
noncomputable def effectiveToDivisor : C.EffDiv →+ C.Divisor :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp]
theorem effectiveToDivisor_apply (D : C.EffDiv) (x : C.Atom) :
    C.effectiveToDivisor D x = (D x : ℤ) := by
  rfl

/-- Passing from an effective divisor to the signed divisor group preserves
its degree.  The right side is merely the natural degree cast to `ℤ`. -/
theorem divisorDegree_effectiveToDivisor (D : C.EffDiv) :
    C.divisorDegree (C.effectiveToDivisor D) = (C.divDegree D : ℤ) := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | @single_add x m D hx hm ih =>
      simp only [map_add, C.divDegree_add, Nat.cast_add, ih]
      rw [C.divDegree_single]
      simp [effectiveToDivisor, divisorDegree]

/-! ## Divisor classes and their degree fibres -/

/-- Divisor classes modulo a specified subgroup of principal divisors.

The subgroup is a genuine parameter rather than an arbitrary equivalence
relation: the concrete curve must generate it from divisors of rational
functions. -/
abbrev DivisorClass (Principal : AddSubgroup C.Divisor) :=
  C.Divisor ⧸ Principal

/-- The class of a signed divisor in the quotient by principal divisors. -/
noncomputable def classOf (Principal : AddSubgroup C.Divisor) :
    C.Divisor →+ C.DivisorClass Principal :=
  QuotientAddGroup.mk' Principal

/-- Divisor degree descends through principal equivalence once every
principal divisor has degree zero. -/
noncomputable def classDegree (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker) :
    C.DivisorClass Principal →+ ℤ :=
  QuotientAddGroup.lift Principal C.divisorDegree hPrincipal

@[simp]
theorem classDegree_classOf
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (D : C.Divisor) :
    C.classDegree Principal hPrincipal (C.classOf Principal D) =
      C.divisorDegree D := by
  rfl

/-- The degree-`n` Picard fibre is the subtype of divisor classes whose
descended degree is exactly `n`.  It is not an unrelated finite type standing
in for the geometric Picard torsor. -/
def PicDegree (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker) (n : ℤ) :=
  {c : C.DivisorClass Principal // C.classDegree Principal hPrincipal c = n}

/-- An effective divisor of degree `n` determines an actual class in the
degree-`n` Picard fibre. -/
noncomputable def effectiveClass
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (n : ℕ) (D : C.EffDivOfDegree n) :
    C.PicDegree Principal hPrincipal n :=
  ⟨C.classOf Principal (C.effectiveToDivisor D.1), by
    rw [C.classDegree_classOf, C.divisorDegree_effectiveToDivisor, D.2]⟩

/-! ## Translation and canonical residual duality -/

/-- Translation by a divisor class of degree `b-a` identifies the degree
`a` and degree `b` Picard fibres.  This is the algebraic content behind the
usual statement that every nonempty `Pic^n` is a torsor under `Pic^0`. -/
noncomputable def picDegreeTranslate
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    {a b : ℤ}
    (t : C.DivisorClass Principal)
    (ht : C.classDegree Principal hPrincipal t = b - a) :
    C.PicDegree Principal hPrincipal a ≃
      C.PicDegree Principal hPrincipal b where
  toFun c := ⟨c.1 + t, by
    rw [map_add, c.2, ht]
    omega⟩
  invFun c := ⟨c.1 - t, by
    rw [map_sub, c.2, ht]
    omega⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- A degree-one divisor class supplies compatible base points in every
Picard degree.  Translating a degree-`n` class by `-n` copies of that base
class identifies `Pic^n` with the degree-zero Picard group. -/
noncomputable def picDegreeEquivZero
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (base : C.DivisorClass Principal)
    (hbase : C.classDegree Principal hPrincipal base = 1)
    (n : ℤ) :
    C.PicDegree Principal hPrincipal n ≃
      C.PicDegree Principal hPrincipal 0 :=
  C.picDegreeTranslate Principal hPrincipal ((-n) • base) (by
    rw [map_zsmul, hbase]
    simp)

/-- A canonical divisor class of degree six gives the genus-four residual
equivalence `Pic^4 ≃ Pic^2` by `L ↦ K-L`.  The map is its own inverse; the
geometric work left to a concrete curve is to prove that the chosen
degree-six class is canonical. -/
noncomputable def residualDegreeFourTwo
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (canonical : C.DivisorClass Principal)
    (hcanonical : C.classDegree Principal hPrincipal canonical = 6) :
    C.PicDegree Principal hPrincipal 4 ≃
      C.PicDegree Principal hPrincipal 2 where
  toFun c := ⟨canonical - c.1, by
    rw [map_sub, hcanonical, c.2]
    norm_num⟩
  invFun c := ⟨canonical - c.1, by
    rw [map_sub, hcanonical, c.2]
    norm_num⟩
  left_inv c := by
    apply Subtype.ext
    change canonical - (canonical - c.1) = c.1
    abel
  right_inv c := by
    apply Subtype.ext
    change canonical - (canonical - c.1) = c.1
    abel

end ClosedPointGrading

/-! ## Kernel certificates for computable divisor-class normal forms -/

/-- A surjective additive normal-form map whose kernel is exactly the
principal-divisor subgroup identifies the corresponding quotient with its
finite normal-form group.

This is the sound interface for a future Gröbner-basis or linear-algebra
divisor reduction algorithm.  Cardinality is not an input: the algorithm must
prove both its exact kernel and surjectivity before the quotient equivalence
is available. -/
noncomputable def quotientAddEquivOfNormalForm
    {D G : Type*} [AddCommGroup D] [AddCommGroup G]
    (Principal : AddSubgroup D)
    (normalForm : D →+ G)
    (hker : normalForm.ker = Principal)
    (hsurjective : Function.Surjective normalForm) :
    (D ⧸ Principal) ≃+ G := by
  subst Principal
  let rangeEquiv : normalForm.range ≃+ G :=
    AddEquiv.ofBijective normalForm.range.subtype ⟨
      Subtype.coe_injective,
      by
        intro g
        obtain ⟨d, rfl⟩ := hsurjective g
        exact ⟨⟨normalForm d, ⟨d, rfl⟩⟩, rfl⟩⟩
  exact (QuotientAddGroup.quotientKerEquivRange normalForm).trans rangeEquiv

end MazurProof.CurveZetaEffectiveDivisors
