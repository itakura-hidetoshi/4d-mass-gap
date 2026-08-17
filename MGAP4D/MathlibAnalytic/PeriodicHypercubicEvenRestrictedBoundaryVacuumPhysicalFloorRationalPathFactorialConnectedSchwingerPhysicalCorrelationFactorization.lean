import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerUniformRealInsertionExtension
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealTwoPointSchwingerExtension

/-!
# Physical-correlation factorization for rational connected Schwinger data

The rational path-law construction and the reconstructed physical OS semigroup now
carry complementary regularity statements:

* rational connected Schwinger functions admit a canonical real-insertion extension
  once uniform continuity is known;
* every symmetric physical OS autocorrelation is globally uniformly continuous on
  nonnegative Euclidean time;
* the actual physical two-point autocorrelation has already been packaged as a
  uniformly continuous function of two real insertion times and identified with
  the canonical extension of its rational restriction.

This file isolates the exact remaining OS-reconstruction identification problem.
If a rational connected Schwinger function factors through an actual physical OS
autocorrelation, its uniform continuity follows by composition.  In the actual
`Fin 2` case, if the rational path-law connected Schwinger function equals the
rational restriction of the physical OS two-point function, then the two canonical
real-insertion functions are equal identically.  Real common-shift invariance then
follows from the physical two-point function itself.

No equality between the path-law correlator and the OS autocorrelation is assumed
silently; the reconstruction equality is exposed explicitly as `hfactor` or
`hreconstruct`.
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

/-- In the actual two-insertion case, an OS reconstruction equality on rational
insertion tuples transfers the already-proved physical two-point regularity to the
path-law connected Schwinger function. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction_twoPoint_uniformContinuous_of_physicalRationalEuclideanTwoPointCorrelation_eq
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
    (O : Fin 2 → ℝ → ℝ)
    (hreconstruct : ∀ time : Fin 2 → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O =
        T.physicalRationalEuclideanTwoPointCorrelation psi time) :
    UniformContinuous
      (fun time : Fin 2 → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O) := by
  have hfun :
      (fun time : Fin 2 → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O) =
      T.physicalRationalEuclideanTwoPointCorrelation psi := by
    funext time
    exact hreconstruct time
  rw [hfun]
  exact T.physicalRationalEuclideanTwoPointCorrelation_uniformContinuous hSymmetric psi

/-- Once the rational two-point OS reconstruction identity is supplied, the
canonical real-insertion extension of the actual path-law connected Schwinger
function is definitionally pinned down by density: it is exactly the already
constructed physical real two-point OS correlation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension_twoPoint_eq_physicalEuclideanTwoPointCorrelation_of_reconstruction
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
    (O : Fin 2 → ℝ → ℝ)
    (hreconstruct : ∀ time : Fin 2 → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O =
        T.physicalRationalEuclideanTwoPointCorrelation psi time) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
        L 2 O =
      T.physicalEuclideanTwoPointCorrelation psi := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
  apply MGAP4D.ratFinUniformlyExtend_unique
  · intro time
    change T.physicalRationalEuclideanTwoPointCorrelation psi time =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure 2 time O
    exact (hreconstruct time).symm
  · exact
      (T.physicalEuclideanTwoPointCorrelation_uniformContinuous hSymmetric psi).continuous

/-- The same rational OS reconstruction identity therefore yields real common-time
translation invariance of the actual path-law two-point connected Schwinger
extension with no additional regularity assumption. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_twoPoint_uniformRealInsertion_realShift_eq_self_of_reconstruction
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
    (O : Fin 2 → ℝ → ℝ)
    (hreconstruct : ∀ time : Fin 2 → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O =
        T.physicalRationalEuclideanTwoPointCorrelation psi time) :
    ∀ (time : Fin 2 → ℝ) (r : ℝ),
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L 2 O (MGAP4D.realCommonShift time r) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L 2 O time := by
  intro time r
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension_twoPoint_eq_physicalEuclideanTwoPointCorrelation_of_reconstruction
    L T hSymmetric psi O hreconstruct]
  exact T.physicalEuclideanTwoPointCorrelation_realCommonShift psi time r

end
end MathlibAnalytic
end MGAP4D
