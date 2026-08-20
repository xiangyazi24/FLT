# N13 Remaining Plan — Specialization Group Homomorphism

## Status as of 2026-08-19

The N13 rational-point theorem (`n13_affine_x_is_cuspidal`) is blocked on
ONE fundamental piece: connecting the generic-fiber Jacobian to the
special-fiber Jacobian via a group homomorphism.

## What IS proved (complete, committed, 0 sorry)

1. TwoSurjective — doubling surjective on J(ℚ) ≅ G
2. trivialKernel_separated — NSeparated (⊥) 2
3. All 284 N13 infrastructure files — 0 sorry
4. normalizedMumford_rationalAbel_eq_pointMumford — normalize of Abel class = point Mumford
5. reduceCurve_cusp — each cusp reduces to its named special cusp
6. specialPointClass_injective — anchored special Abel class determines special point
7. abelJacobi_injective — Abel-Jacobi is injective on curve points
8. FirstJetDoublingCompatibility (for trivial kernel) — proved in N13DischargeWiring
9. PicTwoSetModel has 19 elements (picTwoSetModel_card)
10. N13 good model: affine charts, smooth, Frobenius point counting

## What is NOT proved

### The fundamental gap: `specialize : G →+ J₂`

Need: a group homomorphism from G = ConcretePic(model ℚ₂) to J₂ = J(𝔽₂),
where J₂ is an AddCommGroup of order 19.

### Why this is hard

1. **CharZero blocker**: NormalFormData (unique balanced Mumford) requires
   [CharZero K]. Over ZMod 2, this fails. So no Mumford group law over 𝔽₂.

2. **Model form mismatch**: The SexticMumford framework assumes y² = f(x).
   Over 𝔽₂, the model is y² + (x³+x+1)y = x⁵+x⁴ (can't complete the
   square). The Mumford representation is fundamentally different.

3. **Vertical divisors**: class_eq_iff (well-definedness of spread-line
   specialization) is FALSE for arbitrary spread lines. Two integral models
   of the same generic Picard class can have different special classes,
   differing by vertical divisors.

## Possible approaches (in order of estimated effort)

### Approach A: Computational group law on PicTwoSetModel (3-5 files, ~400 lines)

Build an AddCommGroup on PicTwoSetModel by explicit computation:
- PicTwoSetModel has 19 elements (proved)
- 19 is prime, so any group of order 19 is cyclic ≅ ℤ/19ℤ
- Define the group operation by the CHAR-2 Cantor algorithm on the
  6-point special curve
- Verify group axioms by native_decide on the 19-element set

Then construct `specialize : G →+ PicTwoSetModel`:
- Define on curve points: specialize(rationalAbel P) = specialPointClass(reduceCurve P)
- Extend to G by group structure (since cusps generate G)
- Prove group hom property

### Approach B: Char-2 NormalFormData (5-8 files, ~800 lines)

Build a separate Mumford theory for the char-2 model form y² + hy = g:
- New SemiMumford structure for char-2 (different from SexticMumford)
- Cantor algorithm for char 2 (different reduction rules)
- NormalFormData without CharZero hypothesis
- Group law on Mumford(model 𝔽₂)

Then the specialization is the natural Mumford coefficient reduction.

### Approach C: Direct PointwiseReflection via formal group (2-3 files, ~300 lines)

Avoid the group hom entirely. Prove PointwiseReflection directly:
- Given reduceCurve P = reduceCurve Q (same special reduction)
- Both pointSpreadLine P and pointSpreadLine Q have same specialClass
- Their rationalClasses differ by D = rationalAbel P - rationalAbel Q
- D is in the "kernel of reduction" (formalized without J₂)
- The kernel is pro-2 (from the existing formal-kernel infrastructure)
- G has exponent 19 (from the existing infrastructure, IF we have some red)

The challenge: "D is in the kernel of reduction" needs a well-defined
reduction map. Without a group hom to J₂, the kernel is not a subgroup
of G.

Could work if: define the kernel as {D ∈ G : ∃ L, rationalClass L = D,
specialClass L = specialClass (zero spread)}. This might be a subgroup
if specialClass-0 is additive (which requires the group hom property).

### Approach D: Abstract algebra shortcut (1-2 files, ~200 lines)

Use the fact that G ≅ ℤ/19ℤ (simple group) and SpecialSet has 19 elements.
Define `classify : G → SpecialSet` as ANY injective function.

Since both sets have 19 elements, an injective function exists (by
`Nat.card_eq_nat_card`). Use `Classical.choice` to get one.

Then PointwiseReflection follows from: for any injective function f,
f(a) = f(b) → a = b.

The issue: connecting this ABSTRACT injective function to `reduceCurve`.
Need: the abstract function agrees with specialPointClass ∘ reduceCurve
on curve points. This requires at least: the cusps' classify values
are the correct special classes.

## Recommendation

**Approach A** (computational group law) seems most promising:
- Finite computation on 19 elements
- Can use native_decide for verification
- Doesn't require new Mumford theory
- The char-2 Cantor algorithm is well-known (see e.g., Handbook of
  Elliptic and Hyperelliptic Curve Cryptography)

**Approach D** (abstract shortcut) is the fastest but has a gap in
connecting to reduceCurve.

## Files to modify

- N13DirectEndpoint.lean — replace classify with group-hom-based version
- N13DischargeWiring.lean — close n13_class_eq_iff OR replace entirely
- NEW N13SpecializationGroupHom.lean — the group homomorphism
- NEW N13SpecialFiberGroupLaw.lean — AddCommGroup on PicTwoSetModel (if approach A)
