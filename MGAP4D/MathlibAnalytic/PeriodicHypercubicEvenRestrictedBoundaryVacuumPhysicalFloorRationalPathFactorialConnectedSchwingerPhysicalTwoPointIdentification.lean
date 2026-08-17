import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerPhysicalCorrelationFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealTwoPointSchwingerExtension

/-!
# Identifying the rational connected two-point Schwinger function with the actual OS correlator

The actual symmetric physical OS semigroup now provides a uniformly continuous
real two-insertion function

`S₂ᴼˢ(t₀,t₁) = C_ψ(‖t₁ - t₀‖₊)`

whose rational restriction has that function as its unique canonical Mathlib
dense extension.  This file isolates the remaining same-root reconstruction
obligation as one explicit equality on rational insertion tuples.

Once that equality is supplied for a concrete observable/state pair, no separate
regularity or real-extension hypothesis remains: rational uniform continuity is
inherited from the OS semigroup, and the canonical real connected-Schwinger
extension is literally the already constructed actual OS two-point function.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance connectedSchwingerPhysicalTwoPointIdentificationNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance connectedSchwingerPhysicalTwoPointIdentificationTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance connectedSchwingerPhysicalTwoPointIdentificationCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance connectedSchwingerPhysicalTwoPointIdentificationSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance connectedSchwingerPhysicalTwoPointIdentificationMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance connectedSchwingerPhysicalTwoPointIdentificationBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- If the rational path-law connected two-point Schwinger function is identified
pointwise with the rational restriction of an actual symmetric physical OS
two-point correlation, then its uniform continuity is theorem-generated. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedTwoPointSchwingerFunction_uniformContinuous_of_physicalTwoPoint_identification
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
    (hidentify : ∀ time : Fin 2 → ℚ,
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
    exact hidentify time
  rw [hfun]
  exact
    T.physicalRationalEuclideanTwoPointCorrelation_uniformContinuous
      hSymmetric psi

/-- Under the same-root rational two-point identification, the canonical real
insertion-time extension constructed from the path-law connected Schwinger data
is exactly the actual real OS two-point correlation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedTwoPointSchwingerUniformRealInsertionExtension_eq_physicalEuclideanTwoPointCorrelation_of_identification
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
    (hidentify : ∀ time : Fin 2 → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O =
        T.physicalRationalEuclideanTwoPointCorrelation psi time) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
        L 2 O =
      T.physicalEuclideanTwoPointCorrelation psi := by
  have hfun :
      (fun time : Fin 2 → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O) =
      T.physicalRationalEuclideanTwoPointCorrelation psi := by
    funext time
    exact hidentify time
  calc
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L 2 O =
        MGAP4D.ratFinUniformlyExtend 2
          (fun time : Fin 2 → ℚ =>
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
              L.continuumMeasure.toMeasure 2 time O) := rfl
    _ = MGAP4D.ratFinUniformlyExtend 2
          (T.physicalRationalEuclideanTwoPointCorrelation psi) :=
      congrArg (MGAP4D.ratFinUniformlyExtend 2) hfun
    _ = T.physicalEuclideanTwoPointCorrelation psi :=
      T.ratFinUniformlyExtend_physicalRationalEuclideanTwoPointCorrelation_eq
        hSymmetric psi

/-- Consequently the path-law canonical real two-point extension is invariant
under every common real Euclidean-time translation, with no separate continuity
or extension-existence premise beyond the rational same-root identification. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedTwoPointSchwingerUniformRealInsertionExtension_realCommonShift_of_identification
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
    (hidentify : ∀ time : Fin 2 → ℚ,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure 2 time O =
        T.physicalRationalEuclideanTwoPointCorrelation psi time) :
    ∀ (time : Fin 2 → ℝ) (r : ℝ),
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L 2 O (MGAP4D.realCommonShift time r) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L 2 O time := by
  have hEq :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedTwoPointSchwingerUniformRealInsertionExtension_eq_physicalEuclideanTwoPointCorrelation_of_identification
      L T hSymmetric psi O hidentify
  intro time r
  rw [hEq]
  exact T.physicalEuclideanTwoPointCorrelation_realCommonShift psi time r

end
end MathlibAnalytic
end MGAP4D
