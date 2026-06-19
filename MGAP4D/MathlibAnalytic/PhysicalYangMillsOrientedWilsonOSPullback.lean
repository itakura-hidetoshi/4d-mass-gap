import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantWeakStarReflectionPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Evaluation of an approximating physical observable is exactly integration
of its pullback against the original oriented compact Wilson Gibbs law at the
selected Prokhorov scale. -/
theorem physical_yang_mills_oriented_approximatingExpectation_eq_gibbs_pullback
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra
      (G.toSymmetryLimit L)) :
    physicalYangMillsApproximatingGaugeInvariantExpectation
        (G.toSymmetryLimit L) n O =
      ∫ U,
        (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
          (E.interpolate (L.subsequence n) U)
        ∂(E.system (L.subsequence n)).gibbsMeasure := by
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  change
    (∫ A,
      (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ) A
      ∂Measure.map (E.interpolate (L.subsequence n))
        (E.system (L.subsequence n)).gibbsMeasure) =
      ∫ U,
        (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
          (E.interpolate (L.subsequence n) U)
        ∂(E.system (L.subsequence n)).gibbsMeasure
  exact MeasureTheory.integral_map
    (E.interpolate_measurable (L.subsequence n)).aemeasurable
    ((O : BoundedContinuousFunction E.PhysicalConfiguration ℝ).continuous.
      aestronglyMeasurable)

/-- The same pullback identity stated directly for the physical weak-star state. -/
theorem physical_yang_mills_oriented_approximatingWeakStarState_eq_gibbs_pullback
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra
      (G.toSymmetryLimit L)) :
    physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n O =
      ∫ U,
        (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
          (E.interpolate (L.subsequence n) U)
        ∂(E.system (L.subsequence n)).gibbsMeasure := by
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  exact physical_yang_mills_oriented_approximatingExpectation_eq_gibbs_pullback
    G L n O

/-- The actual compact-group lattice OS form obtained by pulling the physical
quadratic observable `Theta(F) * F` back through interpolation and integrating
against the original oriented Wilson Gibbs law. -/
noncomputable def
    PhysicalYangMillsGaugeInvariantOSReflectionData.orientedWilsonPullbackForm
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) : ℝ :=
  ∫ U,
    ((D.quadraticObservable F :
        physicalYangMillsGaugeInvariantObservableSubalgebra
          (G.toSymmetryLimit L)) :
      BoundedContinuousFunction E.PhysicalConfiguration ℝ)
      (E.interpolate (L.subsequence n) U)
    ∂(E.system (L.subsequence n)).gibbsMeasure

/-- Evaluation of the physical lattice state on the OS quadratic observable is
definitionally the compact Wilson pullback form. -/
theorem physical_yang_mills_oriented_weakStarState_quadratic_eq_pullbackForm
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n (D.quadraticObservable F) =
      D.orientedWilsonPullbackForm G L n F := by
  exact physical_yang_mills_oriented_approximatingWeakStarState_eq_gibbs_pullback
    G L n (D.quadraticObservable F)

/-- The remaining compact-group finite-volume OS input after the pushforward
identity has been theorem-generated. -/
structure PhysicalYangMillsOrientedWilsonOSPullbackCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  finiteReflectionPositive :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      0 ≤ D.orientedWilsonPullbackForm G L n F

/-- A compact Wilson pullback certificate makes every physical approximating
weak-star state reflection positive. -/
theorem physical_yang_mills_oriented_pullback_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSPullbackCertificate G L D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) := by
  intro F
  rw [physical_yang_mills_oriented_weakStarState_quadratic_eq_pullbackForm]
  exact C.finiteReflectionPositive n F

/-- Finite compact Wilson pullback positivity transfers to the physical
continuum state through the already established weak-star convergence. -/
theorem physical_yang_mills_oriented_pullback_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSPullbackCertificate G L D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) := by
  apply physical_yang_mills_gaugeInvariantWeakStarReflectionPositivity_passes_to_limit
    (G.toSymmetryLimit L) D
  intro n
  exact physical_yang_mills_oriented_pullback_approximating_reflectionPositive
    G L D C n

end

end MathlibAnalytic
end MGAP4D
