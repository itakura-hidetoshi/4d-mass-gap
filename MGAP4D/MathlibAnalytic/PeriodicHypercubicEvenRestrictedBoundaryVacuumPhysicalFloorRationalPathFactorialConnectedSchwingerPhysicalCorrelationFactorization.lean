import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerUniformRealInsertionExtension
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUniformContinuity

/-!
# Physical-correlation factorization for rational connected Schwinger data

The rational path-law construction and the reconstructed physical OS semigroup now
carry complementary regularity statements:

* rational connected Schwinger functions admit a canonical real-insertion extension
  once uniform continuity is known;
* every symmetric physical OS autocorrelation is globally uniformly continuous on
  nonnegative Euclidean time.

This file isolates the exact remaining identification problem.  If a rational
connected Schwinger function factors through a uniformly continuous nonnegative-time
parameter and an actual physical OS autocorrelation, then its uniform continuity is
not a new hypothesis: it follows by composition.  Consequently the canonical real
insertion-time extension is stationary under every real common translation.

No equality between the path-law correlator and the OS autocorrelation is assumed
silently; that equality is exposed as the explicit `hfactor` interface.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance connectedSchwingerPhysicalCorrelationFactorizationNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance connectedSchwingerPhysicalCorrelationFactorizationTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance connectedSchwingerPhysicalCorrelationFactorizationCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance connectedSchwingerPhysicalCorrelationFactorizationSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance connectedSchwingerPhysicalCorrelationFactorizationMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance connectedSchwingerPhysicalCorrelationFactorizationBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- If the actual rational connected Schwinger function factors through a uniformly
continuous nonnegative-time parameter and a symmetric physical OS autocorrelation,
then its uniform continuity is inherited from the physical semigroup. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction_uniformContinuous_of_physicalCorrelation_factorization
    {H : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {physicalVolume : ℕ → ℝ}
    {physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop}
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (tau : (Fin n → ℚ) → NNReal)
    (htau : UniformContinuous tau)
    (hfactor : ∀ time : Fin n → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O =
        T.physicalCorrelation psi (tau time)) :
    UniformContinuous
      (fun time : Fin n → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O) := by
  have hfun :
      (fun time : Fin n → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O) =
      (fun time : Fin n → ℚ => T.physicalCorrelation psi (tau time)) := by
    funext time
    exact hfactor time
  rw [hfun]
  exact (T.physicalCorrelation_uniformContinuous hSymmetric psi).comp htau

/-- A physical-correlation factorization discharges the analytic hypothesis in the
canonical real-insertion extension theorem.  The resulting connected Schwinger
extension is invariant under every real common translation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_uniformRealInsertion_realShift_eq_self_of_physicalCorrelation_factorization
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (tau : (Fin n → ℚ) → NNReal)
    (htau : UniformContinuous tau)
    (hfactor : ∀ time : Fin n → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O =
        T.physicalCorrelation psi (tau time)) :
    ∀ (time : Fin n → ℝ) (r : ℝ),
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L n O (MGAP4D.realCommonShift time r) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L n O time := by
  apply
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_uniformRealInsertion_realShift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n O
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction_uniformContinuous_of_physicalCorrelation_factorization
      L T hSymmetric psi n O tau htau hfactor

end
end MathlibAnalytic
end MGAP4D
