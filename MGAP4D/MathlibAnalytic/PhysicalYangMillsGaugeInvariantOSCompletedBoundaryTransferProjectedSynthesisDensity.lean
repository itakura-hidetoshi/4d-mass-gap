import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonRealizableOneStepCoherence
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance projectedBoundarySynthesisDensitySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance projectedBoundarySynthesisDensitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance projectedBoundarySynthesisDensitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance projectedBoundarySynthesisDensitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance projectedBoundarySynthesisDensitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectedBoundarySynthesisDensitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The canonical completed OS state associated with an arbitrary ambient
boundary-Haar vector: orthogonally project to the completed OS boundary image
and apply the isometric inverse on that closed range. -/
noncomputable def completedBoundaryProjectedPhysicalState
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) (y : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert :=
  realLinearIsometryProjectedInverse
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) y

/-- The whole-space completed boundary transfer is exactly the physical OS
operator applied to the projected physical state of its ambient input. -/
theorem completedBoundaryTransfer_apply_eq_projectedPhysicalState
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (y : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    Q.completedBoundaryTransfer hInvariant C n t y =
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (C.finiteOperator n (t / 2)
          (Q.completedBoundaryProjectedPhysicalState hInvariant n y)) := by
  rfl

/-- Replacing an arbitrary boundary input by the embedded projected physical
state does not change the completed boundary transfer. -/
theorem completedBoundaryTransfer_apply_embeddedProjectedPhysicalState
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (y : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    Q.completedBoundaryTransfer hInvariant C n t
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Q.completedBoundaryProjectedPhysicalState hInvariant n y)) =
      Q.completedBoundaryTransfer hInvariant C n t y := by
  rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
  exact Q.completedBoundaryTransfer_apply_eq_projectedPhysicalState hInvariant C n t y |>.symm

/-- The dense actual-synthesis approximation therefore extends from embedded
completed OS states to every ambient boundary-Haar input.  No range membership
or surjectivity of the boundary isometry is assumed. -/
theorem exists_actualSynthesis_translatedPositiveHalf_tendsto_completedBoundaryTransfer_boundary
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (y : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ∃ F : ℕ → (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto (fun k => (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState (F k)) atTop
        (𝓝 (Q.completedBoundaryProjectedPhysicalState hInvariant n y)) ∧
      Tendsto
        (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
          (Q.translatedPositiveHalfL2LinearMap hInvariant C n t (F k)))
        atTop (𝓝 (Q.completedBoundaryTransfer hInvariant C n t y)) := by
  rcases Q.exists_actualSynthesis_translatedPositiveHalf_tendsto_completedBoundaryTransfer
      hInvariant C n t (Q.completedBoundaryProjectedPhysicalState hInvariant n y) with
    ⟨F, hstate, hvec⟩
  refine ⟨F, hstate, ?_⟩
  simpa only [Q.completedBoundaryTransfer_apply_embeddedProjectedPhysicalState
    hInvariant C n t y] using hvec

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- Under the minimal common/realizable one-step seam, every ambient boundary
input has a dense raw-carrier sequence whose actual finite-time dynamics is one
literal realizable lattice step and whose synthesis converges to the projected
completed transfer at time `2`. -/
theorem exists_actualSynthesis_realizableOneStep_tendsto_completedBoundaryTransfer_two_boundary
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (y : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ∃ F : ℕ → (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto (fun k => (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState (F k)) atTop
        (𝓝 (Q.completedBoundaryProjectedPhysicalState hInvariant n y)) ∧
      Tendsto
        (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
          (Q.positiveHalfL2LinearMap hInvariant n
            (R.realizableCarrierTranslation hInvariant n 1 (F k))))
        atTop (𝓝 (Q.completedBoundaryTransfer hInvariant C n 2 y)) := by
  rcases Q.exists_actualSynthesis_translatedPositiveHalf_tendsto_completedBoundaryTransfer_boundary
      hInvariant C n 2 y with ⟨F, hstate, hvec⟩
  refine ⟨F, hstate, ?_⟩
  have hfun :
      (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1 (F k)))) =
      (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
        (Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 (F k))) := by
    funext k
    exact congrArg
      (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n)
      (R.translatedPositiveHalfL2LinearMap_two_apply_eq_realizableOneStep
        hInvariant C n hCoherent (F k)).symm
  rw [hfun]
  exact hvec

/-- Exact endpoint-pair form for an arbitrary pair-Haar input `x` and arbitrary
test vector `z`.  The left completed coefficient is now a scalar limit of
actual realizable one-step Wilson synthesis coefficients, with no assumption
that `x` itself lies in the completed OS boundary image. -/
theorem exists_actualSynthesis_realizableOneStep_pair_inner_tendsto_completedBoundaryTransfer_two_pair
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (x z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent n) N) :
    ∃ F : ℕ → (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto (fun k => (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState (F k)) atTop
        (𝓝 (Q.completedBoundaryProjectedPhysicalState hInvariant n
          (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry (halfExtent n) N x))) ∧
      Tendsto
        (fun k => inner ℝ
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry (halfExtent n) N
            (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
              (Q.positiveHalfL2LinearMap hInvariant n
                (R.realizableCarrierTranslation hInvariant n 1 (F k))))) z)
        atTop
        (𝓝 (inner ℝ
          (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair (halfExtent n) N
            (Q.completedBoundaryTransfer hInvariant C n 2) x) z)) := by
  let y := periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
    (halfExtent n) N x
  rcases R.exists_actualSynthesis_realizableOneStep_tendsto_completedBoundaryTransfer_two_boundary
      hInvariant C n hCoherent y with ⟨F, hstate, hvec⟩
  refine ⟨F, hstate, ?_⟩
  have hpair : Tendsto
      (fun k => periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
        (halfExtent n) N
        (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
          (Q.positiveHalfL2LinearMap hInvariant n
            (R.realizableCarrierTranslation hInvariant n 1 (F k)))))
      atTop
      (𝓝 (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
        (halfExtent n) N
        (Q.completedBoundaryTransfer hInvariant C n 2 y))) :=
    (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N).continuous.continuousAt.tendsto.comp hvec
  have hz : Tendsto
      (fun _ : ℕ => z) atTop (𝓝 z) :=
    tendsto_const_nhds
  have hinner : Tendsto
      (fun k => inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
            halfExtent N hN beta hbeta n
            (Q.positiveHalfL2LinearMap hInvariant n
              (R.realizableCarrierTranslation hInvariant n 1 (F k))))) z)
      atTop
      (𝓝 (inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2 y)) z)) :=
    hpair.inner hz
  simpa only [y, periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_apply] using hinner

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

end MathlibAnalytic
end MGAP4D

end
