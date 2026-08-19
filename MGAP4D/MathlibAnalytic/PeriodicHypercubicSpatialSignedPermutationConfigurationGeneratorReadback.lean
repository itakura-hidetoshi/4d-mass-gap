import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpatialSignedPermutationConfiguration

/-!
# Generator readback for the abstract signed-spatial configuration pullback

The generic configuration pullback is defined through the signed boundary-step preimage under an
arbitrary element of the abstract 48-element signed-coordinate group.  The finite Wilson route
already has concrete configuration actions for the two adjacent spatial swaps and reflection of the
first spatial axis.  This file proves that the new generic construction recovers those existing
same-root actions exactly.

The proof first records that the three distinguished abstract generators are involutions, then
identifies their signed positive-edge images, and finally reads those images through the canonical
`periodicHypercubicStepValue`.

No new symmetry assumption, plaquette-holonomy theorem, cubic irrep label, continuum-spin claim, or
spectral statement is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract adjacent swap `(1,2)` is an involution in the signed-permutation group. -/
@[simp]
theorem spatialSignedPermutationSwap12_inv :
    spatialSignedPermutationSwap12⁻¹ = spatialSignedPermutationSwap12 := by
  apply SemidirectProduct.ext
  · funext i
    fin_cases i <;>
      simp [spatialSignedPermutationSwap12, spatialAxisPositiveSign,
        spatialAxisPermutationSignAction_apply]
  · simp [spatialSignedPermutationSwap12]

/-- Abstract adjacent swap `(2,3)` is an involution in the signed-permutation group. -/
@[simp]
theorem spatialSignedPermutationSwap23_inv :
    spatialSignedPermutationSwap23⁻¹ = spatialSignedPermutationSwap23 := by
  apply SemidirectProduct.ext
  · funext i
    fin_cases i <;>
      simp [spatialSignedPermutationSwap23, spatialAxisPositiveSign,
        spatialAxisPermutationSignAction_apply]
  · simp [spatialSignedPermutationSwap23]

/-- Abstract reflection of the first spatial coordinate is an involution. -/
@[simp]
theorem spatialSignedPermutationReflect1_inv :
    spatialSignedPermutationReflect1⁻¹ = spatialSignedPermutationReflect1 := by
  apply SemidirectProduct.ext
  · funext i
    fin_cases i <;>
      simp [spatialSignedPermutationReflect1, spatialAxisReflect1Sign,
        spatialAxisPermutationSignAction_apply]
  · simp [spatialSignedPermutationReflect1]

/-- The generic signed edge image of `swap12` is exactly the already-canonical positive-edge swap,
with forward orientation. -/
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_swap12
    (n : ℕ)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n
        spatialSignedPermutationSwap12 e =
      { edge := periodicHypercubicEdgeSpatialAxisSwap12Equiv n e
        orientation := .forward } := by
  rcases e with ⟨x, μ⟩
  refine Fin.cases ?_ (fun k => ?_) μ
  · simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
      periodicHypercubicEdgeSpatialAxisSwap12Equiv_apply,
      periodicHypercubicVertexSpatialSignedPermutation_swap12]
  · fin_cases k <;>
      simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
        periodicHypercubicSpatialSignedPermutationAxis,
        periodicHypercubicEdgeSpatialAxisSwap12Equiv_apply,
        periodicHypercubicVertexSpatialSignedPermutation_swap12,
        spatialSignedPermutationSwap12, spatialAxisPositiveSign]

/-- The generic signed edge image of `swap23` is exactly the already-canonical positive-edge swap,
with forward orientation. -/
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_swap23
    (n : ℕ)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n
        spatialSignedPermutationSwap23 e =
      { edge := periodicHypercubicEdgeSpatialAxisSwap23Equiv n e
        orientation := .forward } := by
  rcases e with ⟨x, μ⟩
  refine Fin.cases ?_ (fun k => ?_) μ
  · simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
      periodicHypercubicEdgeSpatialAxisSwap23Equiv_apply,
      periodicHypercubicVertexSpatialSignedPermutation_swap23]
  · fin_cases k <;>
      simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
        periodicHypercubicSpatialSignedPermutationAxis,
        periodicHypercubicEdgeSpatialAxisSwap23Equiv_apply,
        periodicHypercubicVertexSpatialSignedPermutation_swap23,
        spatialSignedPermutationSwap23, spatialAxisPositiveSign]

/-- The generic signed edge image of first-axis reflection is exactly the concrete positive-edge
representative, with backward orientation precisely for physical axis `1`. -/
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_reflect1
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep
        (PeriodicHypercubicEvenSideLength H)
        spatialSignedPermutationReflect1 e =
      if e.2 = 1 then
        { edge := periodicHypercubicEvenEdgeSpatialAxis1Reflection H e
          orientation := .backward }
      else
        { edge := periodicHypercubicEvenEdgeSpatialAxis1Reflection H e
          orientation := .forward } := by
  rcases e with ⟨x, μ⟩
  fin_cases μ <;>
    simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
      periodicHypercubicSpatialSignedPermutationAxis,
      periodicHypercubicEvenEdgeSpatialAxis1Reflection,
      periodicHypercubicVertexSpatialSignedPermutation_reflect1,
      spatialSignedPermutationReflect1, spatialAxisReflect1Sign]

/-- Generic abstract `swap12` configuration pullback equals the existing concrete swap action. -/
theorem periodicHypercubicConfigurationSpatialSignedPermutation_swap12
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicConfigurationSpatialSignedPermutation
        spatialSignedPermutationSwap12 A =
      periodicHypercubicConfigurationSpatialAxisSwap12 A := by
  funext e
  simp [periodicHypercubicConfigurationSpatialSignedPermutation,
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_swap12,
    periodicHypercubicStepValue,
    periodicHypercubicConfigurationSpatialAxisSwap12]

/-- Generic abstract `swap23` configuration pullback equals the existing concrete swap action. -/
theorem periodicHypercubicConfigurationSpatialSignedPermutation_swap23
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicConfigurationSpatialSignedPermutation
        spatialSignedPermutationSwap23 A =
      periodicHypercubicConfigurationSpatialAxisSwap23 A := by
  funext e
  simp [periodicHypercubicConfigurationSpatialSignedPermutation,
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_swap23,
    periodicHypercubicStepValue,
    periodicHypercubicConfigurationSpatialAxisSwap23]

/-- Generic abstract first-axis reflection pullback equals the existing concrete finite-lattice
reflection action, including inversion of exactly the reversed axis-`1` link values. -/
theorem periodicHypercubicConfigurationSpatialSignedPermutation_reflect1
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicConfigurationSpatialSignedPermutation
        spatialSignedPermutationReflect1 A =
      periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A := by
  funext e
  by_cases haxis : e.2 = 1
  · simp [periodicHypercubicConfigurationSpatialSignedPermutation,
      periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_reflect1,
      periodicHypercubicStepValue,
      periodicHypercubicEvenConfigurationSpatialAxis1Reflection, haxis]
  · simp [periodicHypercubicConfigurationSpatialSignedPermutation,
      periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_reflect1,
      periodicHypercubicStepValue,
      periodicHypercubicEvenConfigurationSpatialAxis1Reflection, haxis]

end

end MathlibAnalytic
end MGAP4D
