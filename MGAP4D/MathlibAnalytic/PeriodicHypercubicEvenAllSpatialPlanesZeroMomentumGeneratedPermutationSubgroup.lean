import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSignedGeneratorWord
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic

/-!
# Generated permutation subgroup preserves the all-spatial zero-momentum observable

The preceding layer proves scalar invariance for every finite word in the concrete generators
`swap12`, `swap23`, and `reflect1`.  This file upgrades those actions from raw configuration
functions to genuine permutations of the finite positive-link `SU(N)` configuration carrier and
then takes the subgroup they generate inside its full permutation group.

The two axis swaps are lifted using the already-canonical edge equivalences: forward pullback is the
observable action and inverse pullback uses the forward edge equivalence.  The axis-`1` reflection
uses its already-proved involution directly.  `Subgroup.closure_induction` then shows that every
permutation in the generated subgroup fixes the scalar all-spatial zero-momentum observable.

This is an actual group-level closure statement on the physical finite configuration carrier.  It
still does not identify the generated subgroup with an abstract hyperoctahedral/cubic group, assign
an `A₁` irrep label, identify continuum spin, or make a spectral mass claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Configuration permutation induced by the `(1 2)` spatial-axis swap. -/
def periodicHypercubicEvenConfigurationSpatialAxisSwap12Equiv
    (H N : ℕ) :
    Equiv.Perm
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := periodicHypercubicConfigurationSpatialAxisSwap12
  invFun := fun A e =>
    A (periodicHypercubicEdgeSpatialAxisSwap12Equiv
      (PeriodicHypercubicEvenSideLength H) e)
  left_inv A := by
    funext e
    simp [periodicHypercubicConfigurationSpatialAxisSwap12]
  right_inv A := by
    funext e
    simp [periodicHypercubicConfigurationSpatialAxisSwap12]

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialAxisSwap12Equiv_apply
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenConfigurationSpatialAxisSwap12Equiv H N A =
      periodicHypercubicConfigurationSpatialAxisSwap12 A :=
  rfl

/-- Configuration permutation induced by the `(2 3)` spatial-axis swap. -/
def periodicHypercubicEvenConfigurationSpatialAxisSwap23Equiv
    (H N : ℕ) :
    Equiv.Perm
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := periodicHypercubicConfigurationSpatialAxisSwap23
  invFun := fun A e =>
    A (periodicHypercubicEdgeSpatialAxisSwap23Equiv
      (PeriodicHypercubicEvenSideLength H) e)
  left_inv A := by
    funext e
    simp [periodicHypercubicConfigurationSpatialAxisSwap23]
  right_inv A := by
    funext e
    simp [periodicHypercubicConfigurationSpatialAxisSwap23]

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialAxisSwap23Equiv_apply
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenConfigurationSpatialAxisSwap23Equiv H N A =
      periodicHypercubicConfigurationSpatialAxisSwap23 A :=
  rfl

/-- Configuration permutation induced by reflection of spatial axis `1`. -/
def periodicHypercubicEvenConfigurationSpatialAxis1ReflectionEquiv
    (H N : ℕ) :
    Equiv.Perm
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := periodicHypercubicEvenConfigurationSpatialAxis1Reflection H
  invFun := periodicHypercubicEvenConfigurationSpatialAxis1Reflection H
  left_inv := periodicHypercubicEvenConfigurationSpatialAxis1Reflection_involutive H
  right_inv := periodicHypercubicEvenConfigurationSpatialAxis1Reflection_involutive H

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialAxis1ReflectionEquiv_apply
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenConfigurationSpatialAxis1ReflectionEquiv H N A =
      periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A :=
  rfl

/-- Genuine configuration permutation corresponding to one concrete signed-spatial generator. -/
def periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv
    (H N : ℕ)
    (g : PeriodicHypercubicEvenSpatialSignedGenerator) :
    Equiv.Perm
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  match g with
  | .swap12 => periodicHypercubicEvenConfigurationSpatialAxisSwap12Equiv H N
  | .swap23 => periodicHypercubicEvenConfigurationSpatialAxisSwap23Equiv H N
  | .reflect1 => periodicHypercubicEvenConfigurationSpatialAxis1ReflectionEquiv H N

@[simp]
theorem periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv_apply
    (H N : ℕ)
    (g : PeriodicHypercubicEvenSpatialSignedGenerator)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv H N g A =
      periodicHypercubicEvenSpatialSignedGeneratorAction g A := by
  cases g <;> rfl

/-- The actual subgroup of configuration permutations generated by the two adjacent swaps and one
independent spatial reflection. -/
def periodicHypercubicEvenGeneratedSignedSpatialPermutationSubgroup
    (H N : ℕ) :
    Subgroup
      (Equiv.Perm
        (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  Subgroup.closure
    (Set.range (periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv H N))

/-- Each concrete generator lies in the generated configuration-permutation subgroup. -/
theorem periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv_mem_generated
    (H N : ℕ)
    (g : PeriodicHypercubicEvenSpatialSignedGenerator) :
    periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv H N g ∈
      periodicHypercubicEvenGeneratedSignedSpatialPermutationSubgroup H N :=
  Subgroup.subset_closure ⟨g, rfl⟩

/-- Every permutation in the generated subgroup fixes the concrete all-spatial zero-momentum
normalized-real-trace observable. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_generatedPermutationSubgroupInvariant
    (H N : ℕ)
    (σ : periodicHypercubicEvenGeneratedSignedSpatialPermutationSubgroup H N)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        ((σ : Equiv.Perm
          (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)) A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  let P :
      Equiv.Perm
          (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) → Prop :=
    fun e => ∀ A,
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N (e A) =
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A
  have hgen :
      ∀ e ∈ Set.range
          (periodicHypercubicEvenSpatialSignedGeneratorConfigurationEquiv H N), P e := by
    rintro e ⟨g, rfl⟩ B
    simpa using
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_signedGeneratorInvariant
        H N g B
  have hone : P 1 := by
    intro B
    rfl
  have hmul :
      ∀ x y,
        x ∈ periodicHypercubicEvenGeneratedSignedSpatialPermutationSubgroup H N →
        y ∈ periodicHypercubicEvenGeneratedSignedSpatialPermutationSubgroup H N →
        P x → P y → P (x * y) := by
    intro x y _hxmem _hymem hx hy B
    simpa using (hx (y B)).trans (hy B)
  have hinv :
      ∀ x,
        x ∈ periodicHypercubicEvenGeneratedSignedSpatialPermutationSubgroup H N →
        P x → P x⁻¹ := by
    intro x _hxmem hx B
    have h := hx (x⁻¹ B)
    have h' :
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N B =
          periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N (x⁻¹ B) := by
      simpa using h
    exact h'.symm
  exact
    Subgroup.closure_induction hgen hone hmul hinv σ.property A

end

end MathlibAnalytic
end MGAP4D
