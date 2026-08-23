import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalReflectionInvariance
import Mathlib.Analysis.Normed.Operator.Extend

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance actualCanonicalCompletedBoundarySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualCanonicalCompletedBoundarySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualCanonicalCompletedBoundarySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualCanonicalCompletedBoundarySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualCanonicalCompletedBoundarySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualCanonicalCompletedBoundarySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Extend the automatic separated Wilson boundary isometry continuously from
the dense OS quotient to the completed physical Hilbert space. -/
noncomputable def toCompletedBoundaryMomentContinuousLinearMapAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N := by
  let P :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
  let e : P.Separated →L[ℝ] P.PhysicalHilbert := by
    change P.Separated →L[ℝ] UniformSpace.Completion P.Separated
    exact UniformSpace.Completion.toComplL
  exact ContinuousLinearMap.extend
    (R.toSeparatedBoundaryMomentLinearIsometryAutomatic n).toContinuousLinearMap e

/-- On the dense separated quotient, the completed boundary map is exactly the
existing automatic separated boundary isometry. -/
@[simp] theorem toCompletedBoundaryMomentContinuousLinearMapAutomatic_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Separated) :
    R.toCompletedBoundaryMomentContinuousLinearMapAutomatic n
        (x : UniformSpace.Completion
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S R.reflectionData halfExtent N hN beta hbeta
              R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
              R.approximatingReflectionInvariantFamily n).Separated) =
      R.toSeparatedBoundaryMomentLinearIsometryAutomatic n x := by
  let P :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
  let e : P.Separated →L[ℝ] P.PhysicalHilbert := by
    change P.Separated →L[ℝ] UniformSpace.Completion P.Separated
    exact UniformSpace.Completion.toComplL
  have hDense : DenseRange e := by
    change DenseRange
      (fun y : P.Separated =>
        (y : UniformSpace.Completion P.Separated))
    exact P.separated_dense_in_physical
  have hInducing : IsUniformInducing e := by
    change IsUniformInducing
      ((↑) : P.Separated → UniformSpace.Completion P.Separated)
    exact UniformSpace.Completion.isUniformInducing_coe P.Separated
  change ContinuousLinearMap.extend
      (R.toSeparatedBoundaryMomentLinearIsometryAutomatic n).toContinuousLinearMap e
        (e x) =
    R.toSeparatedBoundaryMomentLinearIsometryAutomatic n x
  exact ContinuousLinearMap.extend_eq
    (R.toSeparatedBoundaryMomentLinearIsometryAutomatic n).toContinuousLinearMap
      hDense hInducing x

/-- The continuous extension preserves the norm on the entire completed OS
Hilbert space.  The equality is closed and holds on the dense canonical image,
where it reduces to the separated boundary isometry. -/
theorem norm_toCompletedBoundaryMomentContinuousLinearMapAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert) :
    ‖R.toCompletedBoundaryMomentContinuousLinearMapAutomatic n x‖ = ‖x‖ := by
  let P :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
  change UniformSpace.Completion P.Separated at x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (R.toCompletedBoundaryMomentContinuousLinearMapAutomatic n).continuous.norm
      continuous_norm
  · intro y
    rw [R.toCompletedBoundaryMomentContinuousLinearMapAutomatic_coe n y]
    simpa only [UniformSpace.Completion.norm_coe] using
      (R.toSeparatedBoundaryMomentLinearIsometryAutomatic n).norm_map y

/-- The completed physical OS Hilbert space embeds linearly and isometrically in
the actual Wilson boundary `L²` space.  No boundary-surjectivity claim is made. -/
noncomputable def toCompletedBoundaryMomentLinearIsometryAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toLinearMap :=
    (R.toCompletedBoundaryMomentContinuousLinearMapAutomatic n).toLinearMap
  norm_map' := R.norm_toCompletedBoundaryMomentContinuousLinearMapAutomatic n

@[simp] theorem toCompletedBoundaryMomentLinearIsometryAutomatic_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Separated) :
    R.toCompletedBoundaryMomentLinearIsometryAutomatic n
        (x : UniformSpace.Completion
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S R.reflectionData halfExtent N hN beta hbeta
              R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
              R.approximatingReflectionInvariantFamily n).Separated) =
      R.toSeparatedBoundaryMomentLinearIsometryAutomatic n x := by
  exact R.toCompletedBoundaryMomentContinuousLinearMapAutomatic_coe n x

/-- On every dense physical state represented by an actual positive-time
observable, the completed isometry agrees with the canonical Wilson boundary
moment constructed before completion. -/
@[simp] theorem toCompletedBoundaryMomentLinearIsometryAutomatic_physicalState
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Carrier) :
    R.toCompletedBoundaryMomentLinearIsometryAutomatic n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n).physicalState F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S R.reflectionData halfExtent N hN beta hbeta
          R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
          R.approximatingReflectionInvariantFamily n F := by
  let P :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
  change R.toCompletedBoundaryMomentLinearIsometryAutomatic n
      ((SeparationQuotient.mk F : P.Separated) :
        UniformSpace.Completion P.Separated) = _
  rw [R.toCompletedBoundaryMomentLinearIsometryAutomatic_coe n]
  exact R.toSeparatedBoundaryMomentLinearIsometryAutomatic_mk n F

/-- Because the completed OS domain is complete and the boundary realization is
an isometry, its image is a closed subset of boundary `L²`.  Together with
linearity this realizes the physical OS Hilbert space as a closed linear
subspace, without asserting that the range is all of boundary `L²`. -/
theorem isClosed_range_toCompletedBoundaryMomentLinearIsometryAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    IsClosed (Set.range (R.toCompletedBoundaryMomentLinearIsometryAutomatic n)) :=
  (R.toCompletedBoundaryMomentLinearIsometryAutomatic n).isometry
    |>.isClosedEmbedding.isClosed_range

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
