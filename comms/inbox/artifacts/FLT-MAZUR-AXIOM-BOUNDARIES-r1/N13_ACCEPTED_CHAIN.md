# Accepted N13 exact dependency chain

STATUS: COMPLETED BY LEAD at 22f88d43187caf0e57affcc6ded92cdf9b49714a, confirmed by r5 receipt at 1222d33fa09e5a00d29c6ad294f3dfb32baf26ce. This document preserves the dependency-ordered exact statements prepared immediately before that receipt. The final import/axiom replacement below has now been performed by the lead and the fresh aggregate/root axiom audit passed. It is a record of the accepted route, not the next task. Do not redo this integration.


## Scope and stopping condition

The nearest target is exactly:

```lean
MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal :
  ∀ X Y : ℚ, MazurProof.N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1
```

Do not weaken it to a statement assuming separatedness, existence of a compatible reduction, a norm comparison, a pole bound, or first-jet compatibility. Those inputs are constructed along the route below.

The requested baseline is 6aef0f8bdea96652f4879d0f74acd6bf189f306c. The final four modules below are absent there. They are present at later commit [62968808d859114cb9ed61b478d1d692b3e71c52](https://github.com/xiangyazi24/FLT/commit/62968808d859114cb9ed61b478d1d692b3e71c52), whose commit sequence reports completion of the 57-module compilation pass. This plan follows existing tracked statements, not a proposal to create parallel scaffolding or repeat completed arithmetic work.

Stop when the lead has:
1. validated the exact constructed affine theorem's fresh emitted dependencies
2. substituted that theorem for the active axiom without changing its proposition
3. built the actual root and emitted its fresh dependency closure from matching sources/artifacts

A clean constructed theorem alone is not the root acceptance condition. No whole-Mazur completion is claimed: N25, N49, and the prime tail remain.

## 1. Retain the actual geometric producers (already at baseline)

File N13ConstructedReductionClassifier.lean:46–50 constructs:

```lean
def MazurProof.N13ConstructedReductionClassifier.compatibleReduction :
    MazurProof.N13RationalPointEndgame.CompatibleReduction
```

Its actual fields are the constructed classifier, proper curve reduction, `chosen_point_specialClass`, and `reduceCurve_cusp`. No classifier or curve-compatibility premise is supplied by the caller.

File N13ConstructedMappedSpecialFamily.lean:20–50 constructs the exact actual-kernel family. In its original namespace and open context:

```lean
theorem representative_nonempty (z : Kernel) :
    Nonempty (MappedSpecialRepresentative
      (N13TwoAdicAbelChartSection.subgroupToPic Kernel z))

def mappedSpecialFamily : MappedSpecialFamily Kernel

def nearBaseFamily : NearBaseFamily Kernel

theorem nearBaseFamily_realizes (z : Kernel) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic (nearBaseFamily.pair z) =
      N13TwoAdicAbelChartSection.subgroupToPic Kernel z
```

`Kernel` here is the actual constructed specialization kernel, not a freely chosen surrogate. The family is produced from the calibrated chooser, graph contraction, balanced graph, and Hensel graph recovery. Preserve that exact family through K2.

## 2. Descend the same selected norm to integral coefficients

[N13IntegralMatchedNorm.lean](https://github.com/xiangyazi24/FLT/blob/62968808d859114cb9ed61b478d1d692b3e71c52/FLT/Assumptions/MazurProof/N13IntegralMatchedNorm.lean#L23-L97), namespace `MazurProof.N13IntegralMatchedNorm`.

The original context opens `Polynomial N13CenteredPrincipalNumerator N13ActualHermiteEquations`, with `R₂ := ℤ_[2]`, `U := N13AbelChartBase.baseSmoothMumford.u`, and the existing field `K` / coefficient map `c`. The exact integral norm polynomial is:

```lean
def normPoly (A b : R₂[X]) : R₂[X] :=
  (U * A) ^ 2 - (U * A) * b * N13GeneralizedMumfordIntegral.hPoly -
    b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly
```

Dependency order: `norm_map` and the unit/nonvanishing result establish the leading coefficient; leading coefficients determine the scalar exactly; coefficient-map injectivity descends the identity. Exact significant statements:

```lean
theorem norm_leading (P : DiskPair) (d₀ d₁ e₀ e₁ : R₂)
    (he₁ : e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P) :
    (normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁)).leadingCoeff = 1 - e₁

theorem descend_actual_norm
    (P Q : DiskPair) (A b : K[X]) (t : K) (ht : t ≠ 0)
    (d₀ d₁ e₀ e₁ : R₂)
    (hA : A = C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c)
    (hb : b = C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c)
    (he₁ : e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P)
    (k : Kˣ)
    (hnorm : ((X ^ 2 + X) * A) ^ 2 -
        ((X ^ 2 + X) * A) * b * N13GeneralizedMumfordIntegral.hPoly -
        b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
      C (k : K) * (P.u.map c) ^ 2 * (X ^ 2 + X) * Q.u.map c) :
    normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁) =
        C (1 - e₁) * P.u ^ 2 * U * Q.u
```

The scalar is **1-e₁**, not an untracked existential unit. The proof cancels the same nonzero scale t² obtained from the normalized selected numerator. Do not independently choose another multiplier for the norm identity.

## 3. Convert retained bounds to the coefficientwise consumer hypotheses

[N13IntegralHermiteCoefficientBounds.lean:28–48](https://github.com/xiangyazi24/FLT/blob/62968808d859114cb9ed61b478d1d692b3e71c52/FLT/Assumptions/MazurProof/N13IntegralHermiteCoefficientBounds.lean#L28-L48), namespace `MazurProof.N13IntegralHermiteCoefficientBounds`.

Original open context: `Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility`.

```lean
theorem quad_monic (a b : R₂) : (quad a b).Monic

theorem lin_coefficients_mem (P : DiskPair) (e₀ e₁ : R₂)
    (he₀ : e₀ ∈ I P * I P) (he₁ : e₁ ∈ I P * I P) :
    ∀ n, (lin e₀ e₁).coeff n ∈ I P * I P

theorem centered_coefficients_mem (P : DiskPair) (d₀ d₁ : R₂)
    (hd₀ : d₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P)
    (hd₁ : d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P) :
    ∀ n, (quad d₀ d₁ - N13MumfordCenteredDoublingJet.centeredSquareU P).coeff n ∈ I P * I P
```

These turn the four explicit Hermite bounds into exactly the ideal-square membership assumptions of the existing centered-norm theorem. They do not add any new assumption to the ultimate affine theorem.

## 4. Assemble cross-coefficient control for the actual doubled class

[N13ConstructedKernelDoubling.lean:23–69](https://github.com/xiangyazi24/FLT/blob/62968808d859114cb9ed61b478d1d692b3e71c52/FLT/Assumptions/MazurProof/N13ConstructedKernelDoubling.lean#L23-L69), namespace `MazurProof.N13ConstructedKernelDoubling`:

```lean
theorem selected_cross_coefficients
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∀ i, ((L.pair z).u ^ 2 - N13AbelChartBase.baseSmoothMumford.u *
        (L.pair (2 • z)).u).coeff i ∈
      N13TwoAdicKernelChart.coordIdeal L.coord z * N13TwoAdicKernelChart.coordIdeal L.coord z
```

The existing proof chain is:
1. `multiplier_of_centered_double` for P = L.pair z and Q = L.pair (2 • z)
2. retain that α and its tensor numerator through `tensor_numerator_mem_product`
3. actual two-infinity orders → `polynomial_bounds`
4. `exists_good_hermite_shape`
5. `normalize_actual_numerator`, retaining the same numerator and scale
6. `norm_of_actual_shape`, explicitly using hα for the same α
7. step 2's `descend_actual_norm`
8. step 3's coefficient bounds and `cross_coefficients_of_norm`

The recorded source includes all these terms and is not a conditional interface stub.

## 5. Package first-jet compatibility and prove actual-kernel separatedness

Same file:72–89, in the same namespace:

```lean
def forFamily
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility L

def firstJetCompatibility :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility
      N13ConstructedMappedSpecialFamily.nearBaseFamily

theorem actual_kernel_separated :
    N18RouteC.Separated.NSeparated N13ConstructedSpecialization.specialization.ker 2
```

`forFamily` uses the cross-coefficient result at indices 1 and 3. `firstJetCompatibility` instantiates it at precisely the family from step 1. The existing `mappedSpecialFamily.separated` theorem then yields separatedness of the actual constructed specialization kernel.

## 6. Transport separatedness to the exact classifier and apply the endgame

[N13ConstructedRationalPointTheorem.lean:20–37](https://github.com/xiangyazi24/FLT/blob/62968808d859114cb9ed61b478d1d692b3e71c52/FLT/Assumptions/MazurProof/N13ConstructedRationalPointTheorem.lean#L20-L37).

Original namespace: `MazurProof.N13ConstructedRationalPointTheorem`.
Original open: `N13ConstructedReductionClassifier`.

These short existing proofs show the final dependency order exactly:

```lean
theorem quotient_kernel_eq :
    compatibleReduction.classifier.red.ker = N13ConstructedSpecialization.specialization.ker := by
  rw [N13ReductionClassifier.Data.red_ker]
  rfl

theorem quotient_kernel_separated :
    N18RouteC.Separated.NSeparated compatibleReduction.classifier.red.ker 2 := by
  rw [quotient_kernel_eq]
  exact N13ConstructedKernelDoubling.actual_kernel_separated

theorem curvePoint_eq_cusp (P : N13RationalPointEndgame.RationalCurvePoint) :
    ∃ c : N13Mumford.Cusp13, P = N13Mumford.cuspPoint c :=
  compatibleReduction.curvePoint_eq_cusp quotient_kernel_separated P

theorem affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 :=
  compatibleReduction.affine_x_is_cuspidal quotient_kernel_separated
```

The projective classification and affine corollary are both present. The affine corollary directly uses the existing compatible-reduction affine endgame; the projective theorem is a companion result, not a necessary extra premise.

## 7. Minimal lead-owned replacement, after the validation gate

Add this import to `CyclicExclusion13.lean`:

```lean
import FLT.Assumptions.MazurProof.N13ConstructedRationalPointTheorem
```

In the existing `MazurProof.CyclicExclusion13` namespace, replace only the axiom declaration by:

```lean
theorem C13Sextic_affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 :=
  N13ConstructedRationalPointTheorem.affine_x_is_cuspidal
```

No hypotheses, quantifiers, conclusion, declaration name, or downstream consumer changes. No new `sorry`, `admit`, custom axiom, or `native_decide`. This is a documented candidate edit only; this research delivery does not modify the Lean source.

Source-only acyclicity check: at 62968808, the constructed theorem's 335-file local import closure contains neither CyclicExclusion13 nor CyclicOrderAssembly nor any literal admission token. Thus this direct import has no cycle in the observed source graph. External libraries and actual emitted proof dependencies still require the lead's fresh check.

## Lead verification request

Use the actual current source and fresh build artifacts, not the 08-12 olean or 08-20 report. Return:
- immutable source commit including any final wiring
- exact build/audit commands, toolchain and Mathlib identities, and freshness evidence
- fresh `#print axioms` for `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal`
- fresh `#print axioms` for the replacement `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
- fresh `#print axioms MazurProof.mazur_torsion_bound`
- declaration-level sorryAx traversal if requested root dependencies include an admission

The source forecast after successful validated wiring is removal of the N13 custom axiom, leaving N25, N49 and the uniform prime tail. That forecast is not an emitted result. A root result of exactly the expected custom set must still be obtained by the lead, not inferred from this plan or from file import counts.

