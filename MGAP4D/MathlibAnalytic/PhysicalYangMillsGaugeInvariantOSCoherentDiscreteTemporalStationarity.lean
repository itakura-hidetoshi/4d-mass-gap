import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumEuclideanTimeTranslation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation

noncomputable section

open Filter MeasureTheory Set Topology

namespace MGAP4D
namespace MathlibAnalytic

local instance coherentDiscreteTemporalStationaritySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance coherentDiscreteTemporalStationaritySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance coherentDiscreteTemporalStationaritySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance coherentDiscreteTemporalStationaritySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance coherentDiscreteTemporalStationaritySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance coherentDiscreteTemporalStationaritySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Compatibility of the coherent finite-Wilson interpolation with the actual
integer temporal lattice action and the physical Euclidean-time action.

At scale `n`, only the realizable physical times
`(k : ℝ) * S.latticeSpacing n` are required.  No rounding map from real time to
integer lattice time is introduced. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S) : Prop where
  interpolate_integerTemporal_equivariant :
    ∀ (n : ℕ) (k : ℤ)
      (U : PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ),
      Q.interpolate n
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength (halfExtent n)) k U) =
        E.translate ((k : ℝ) * S.latticeSpacing n) (Q.interpolate n U)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- The physical Euclidean time represented by `k` temporal lattice steps at
scale `n`. -/
def realizableTime
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ) (k : ℤ) : ℝ :=
  (k : ℝ) * S.latticeSpacing n

/-- Every actual finite Wilson approximating law is invariant under the physical
Euclidean translation at each realizable integer lattice time.

This is generated solely from:

* the coherent pushforward identification of the approximating law;
* actual finite periodic `SU(N)` Gibbs invariance under integer temporal shifts;
* interpolation equivariance at the realizable time.
-/
theorem approximatingMeasure_map_realizableTime_eq_self
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ) (k : ℤ) :
    Measure.map (E.translate (R.realizableTime n k))
        (S.approximatingMeasure n : Measure S.Configuration) =
      (S.approximatingMeasure n : Measure S.Configuration) := by
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  let μ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      L N hN (beta n) (hbeta n)).gibbsMeasure
  let τ :=
    periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) L k
  rw [Q.approximatingMeasure_toMeasure_eq n]
  calc
    Measure.map (E.translate (R.realizableTime n k))
        (Measure.map (Q.interpolate n) μ) =
      Measure.map
        ((E.translate (R.realizableTime n k)) ∘ Q.interpolate n) μ := by
      exact Measure.map_map
        (E.translate (R.realizableTime n k)).continuous.measurable
        (Q.interpolate_measurable n)
    _ = Measure.map ((Q.interpolate n) ∘ τ) μ := by
      congr 1
      funext U
      exact (R.interpolate_integerTemporal_equivariant n k U).symm
    _ = Measure.map (Q.interpolate n) (Measure.map τ μ) := by
      symm
      exact Measure.map_map
        (Q.interpolate_measurable n)
        τ.measurable
    _ = Measure.map (Q.interpolate n) μ := by
      have hμ : Measure.map τ μ = μ :=
        periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
          L N hN (beta n) (hbeta n) k
      rw [hμ]
      rfl

/-- Every bounded continuous physical observable has invariant expectation under
an actual realizable finite-Wilson Euclidean-time translation. -/
theorem approximating_boundedContinuous_expectation_realizableTime
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ) (k : ℤ)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ X, O (E.translate (R.realizableTime n k) X)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ X, O X
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  calc
    (∫ X, O (E.translate (R.realizableTime n k) X)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ X, O X
        ∂Measure.map (E.translate (R.realizableTime n k))
          (S.approximatingMeasure n : Measure S.Configuration) := by
      symm
      exact MeasureTheory.integral_map
        (E.translate (R.realizableTime n k)).continuous.measurable.aemeasurable
        O.continuous.aestronglyMeasurable
    _ = ∫ X, O X
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
      rw [R.approximatingMeasure_map_realizableTime_eq_self]

/-- Realizable finite-lattice Euclidean translation as an automorphism of the
physical gauge-invariant observable algebra. -/
noncomputable def realizedGaugeInvariantObservableTranslation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ) (k : ℤ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S ≃ₐ[ℝ]
      physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  physicalGaugeInvariantObservablePrecompAlgEquiv S
    (E.translate (R.realizableTime n k))
    (E.gauge_commute (R.realizableTime n k))

/-- The actual finite approximating gauge-invariant state is stationary under
all realizable integer Euclidean-time translations. -/
theorem approximatingGaugeInvariantWeakStarState_realizableTime_invariant
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n : ℕ) (k : ℤ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
        (R.realizedGaugeInvariantObservableTranslation n k O) =
      physicalYangMillsApproximatingGaugeInvariantWeakStarState S n O := by
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
    physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply,
    physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  simpa only [realizedGaugeInvariantObservableTranslation,
    physicalGaugeInvariantObservablePrecompAlgEquiv_apply] using
    R.approximating_boundedContinuous_expectation_realizableTime n k
      (O : BoundedContinuousFunction S.Configuration ℝ)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance

end MathlibAnalytic
end MGAP4D

end
