import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalWeakStarOSState

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumPhysicalOSBilinearLawNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalOSBilinearLawTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalOSBilinearLawCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalOSBilinearLawSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalOSBilinearLawMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalOSBilinearLawBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At every supplied Prokhorov scale, the effective-boundary expectation of an
OS quadratic observable is exactly the diagonal of the existing physical OS
bilinear form built from the approximating weak-star state.

Thus the finite effective boundary law now reaches the literal pre-Hilbert
quadratic form consumed by OS completion, without introducing a second state or
quadratic form. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_osQuadratic_effectiveBoundary_expectation_eq_approximatingOSBilinForm
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L))
    (F : D.positiveTimeSubalgebra)
    (n : ℕ) :
    (∫ b,
      D.quadraticBoundedContinuousFunction F
        (periodicHypercubicEvenBoundaryVacuumMoment
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
      ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n)))) =
      D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState
          (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L) n)
        (F : D.positiveTimeSubalgebra.toSubmodule)
        (F : D.positiveTimeSubalgebra.toSubmodule) := by
  rw [D.osBilinForm_apply]
  simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable] using
    periodicHypercubicEvenRestrictedBoundaryVacuum_osQuadratic_effectiveBoundary_expectation_eq_approximatingWeakStarState
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L D F n

/-- The continuum OS bilinear diagonal is the continuum scalar integral of the
same OS quadratic bounded continuous function.

The continuum measure here is exactly the Prokhorov limit already generated
from the effective-boundary scalar laws. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_continuumOSBilinForm_eq_integral
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L))
    (F : D.positiveTimeSubalgebra) :
    D.osBilinForm
        (physicalYangMillsContinuumGaugeInvariantWeakStarState
          (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L))
        (F : D.positiveTimeSubalgebra.toSubmodule)
        (F : D.positiveTimeSubalgebra.toSubmodule) =
      ∫ x, D.quadraticBoundedContinuousFunction F x
        ∂ProbabilityMeasure.toMeasure L.continuumMeasure := by
  rw [D.osBilinForm_apply]
  rw [physicalYangMillsContinuumGaugeInvariantWeakStarState_apply]
  rfl

/-- The same-root finite effective-boundary quadratic expectations converge
straight to the diagonal of the continuum physical OS bilinear form.

This is the measure-to-state-to-OS-form closure needed before positivity and
Hilbert completion can be consumed. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_osQuadratic_effectiveBoundary_expectation_tendsto_continuumOSBilinForm
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L))
    (F : D.positiveTimeSubalgebra) :
    Tendsto
      (fun n : ℕ =>
        ∫ b,
          D.quadraticBoundedContinuousFunction F
            (periodicHypercubicEvenBoundaryVacuumMoment
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
          ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))))
      atTop
      (nhds
        (D.osBilinForm
          (physicalYangMillsContinuumGaugeInvariantWeakStarState
            (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
              H N hN beta hbeta
              latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
              physicalVolume physicalVolume_tendsto_atTop L))
          (F : D.positiveTimeSubalgebra.toSubmodule)
          (F : D.positiveTimeSubalgebra.toSubmodule))) := by
  simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable] using
    periodicHypercubicEvenRestrictedBoundaryVacuum_osQuadratic_effectiveBoundary_expectation_tendsto_continuumWeakStarState
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L D F

end

end MathlibAnalytic
end MGAP4D
