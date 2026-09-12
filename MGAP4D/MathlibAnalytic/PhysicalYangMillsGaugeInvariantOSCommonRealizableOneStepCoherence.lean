import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferSynthesisDensity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscreteSemigroup
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance commonRealizableOneStepCoherenceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance commonRealizableOneStepCoherenceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance commonRealizableOneStepCoherenceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance commonRealizableOneStepCoherenceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance commonRealizableOneStepCoherenceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance commonRealizableOneStepCoherenceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

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

/-- Minimal model-facing seam between the common all-`NNReal` positive-time
semigroup and the actual finite integer-lattice dynamics at one chosen scale.

Only one lattice step is identified.  No all-real-time realization on the
finite periodic lattice is asserted. -/
def CommonSemigroupOneStepCoherentAt
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) : Prop :=
  C.translate 1 = R.positiveTranslation n 1

/-- The minimal observable-level one-step seam theorem-generates equality of
the corresponding finite OS carrier translations. -/
theorem commonSemigroup_carrierTranslation_one_apply_eq_realizableCarrierTranslation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation 1 F =
      R.realizableCarrierTranslation hInvariant n 1 F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    Pn.carrierOfPositiveTime (C.translate 1 (Pn.positiveTimeElement F)) =
      Pn.carrierOfPositiveTime
        (R.positiveTranslation n 1 (Pn.positiveTimeElement F))
  rw [hCoherent]

/-- At completed-boundary time `2`, the canonical half-time analysis uses
exactly one actual realizable lattice step once the minimal seam is supplied. -/
theorem translatedPositiveHalfL2LinearMap_two_apply_eq_realizableOneStep
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 F =
      Q.positiveHalfL2LinearMap hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1 F) := by
  change
    Q.positiveHalfL2LinearMap hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          ((2 : NNReal) / 2) F) =
      Q.positiveHalfL2LinearMap hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1 F)
  have hhalf : (2 : NNReal) / 2 = 1 := by norm_num
  rw [hhalf,
    R.commonSemigroup_carrierTranslation_one_apply_eq_realizableCarrierTranslation
      hInvariant C n hCoherent F]

/-- The actual Wilson synthesis factor at completed-boundary time `2` is thus
the boundary moment of the actual one-lattice-step translated carrier. -/
theorem actualSynthesis_translatedPositiveHalfL2LinearMap_two_eq_realizableBoundaryMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
        (Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 F) =
      Q.boundaryMomentLinearIsometry hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1 F) := by
  rw [Q.actualSynthesis_translatedPositiveHalfL2LinearMap_apply]
  have hhalf : (2 : NNReal) / 2 = 1 := by norm_num
  rw [hhalf,
    R.commonSemigroup_carrierTranslation_one_apply_eq_realizableCarrierTranslation
      hInvariant C n hCoherent F]

/-- Under the minimal one-step seam, the completion theorem from the preceding
unit has a sequence whose finite-time action is the actual realizable lattice
one-step action rather than the abstract common semigroup action. -/
theorem exists_actualSynthesis_realizableOneStep_tendsto_completedBoundaryTransfer_two
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) :
    ∃ F : ℕ → (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto (fun k => (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState (F k)) atTop (𝓝 psi) ∧
      Tendsto
        (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
          (Q.positiveHalfL2LinearMap hInvariant n
            (R.realizableCarrierTranslation hInvariant n 1 (F k))))
        atTop
        (𝓝 (Q.completedBoundaryTransfer hInvariant C n 2
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi))) := by
  rcases Q.exists_actualSynthesis_translatedPositiveHalf_tendsto_completedBoundaryTransfer
      hInvariant C n 2 psi with ⟨F, hstate, hvec⟩
  refine ⟨F, hstate, ?_⟩
  have hfun :
      (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1 (F k)))) =
      (fun k => physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
        (Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 (F k))) := by
    funext k
    exact congrArg
      (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n)
      (R.translatedPositiveHalfL2LinearMap_two_apply_eq_realizableOneStep
        hInvariant C n hCoherent (F k)).symm
  rw [hfun]
  exact hvec

/-- Scalar endpoint-pair form of the realizable one-step completion theorem.
The test vector is arbitrary in the ambient pair-Haar Hilbert space. -/
theorem exists_actualSynthesis_realizableOneStep_pair_inner_tendsto_completedBoundaryTransfer_two
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent n) N) :
    ∃ F : ℕ → (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto (fun k => (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState (F k)) atTop (𝓝 psi) ∧
      Tendsto
        (fun k => inner ℝ
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry (halfExtent n) N
            (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator halfExtent N hN beta hbeta n
              (Q.positiveHalfL2LinearMap hInvariant n
                (R.realizableCarrierTranslation hInvariant n 1 (F k))))) z)
        atTop
        (𝓝 (inner ℝ
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry (halfExtent n) N
            (Q.completedBoundaryTransfer hInvariant C n 2
              (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi))) z)) := by
  rcases R.exists_actualSynthesis_realizableOneStep_tendsto_completedBoundaryTransfer_two
      hInvariant C n hCoherent psi with ⟨F, hstate, hvec⟩
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
        (Q.completedBoundaryTransfer hInvariant C n 2
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi)))) :=
    (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N).continuous.continuousAt.tendsto.comp hvec
  exact hpair.inner tendsto_const_nhds

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

end MathlibAnalytic
end MGAP4D

end
