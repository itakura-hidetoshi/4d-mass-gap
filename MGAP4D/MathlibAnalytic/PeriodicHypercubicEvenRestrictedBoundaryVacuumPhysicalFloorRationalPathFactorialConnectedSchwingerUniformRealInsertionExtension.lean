import MGAP4D.MathlibAnalytic.RationalFinToRealUniformContinuousExtension
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerRealInsertionStationarity

/-!
# Constructing real insertion-time connected Schwinger extensions

The previous real-insertion stationarity theorem assumes a continuous real-tuple
extension.  Here that extension is constructed canonically from the actual
rational connected Schwinger function under the concrete analytic condition that
the rational-tuple function is uniformly continuous.

Thus the remaining physical/analytic obligation is reduced from existence of an
unspecified real extension to a quantitative regularity statement on the already
constructed rational Schwinger data.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerUniformRealInsertionNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerUniformRealInsertionTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerUniformRealInsertionCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerUniformRealInsertionSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerUniformRealInsertionMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerUniformRealInsertionBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Canonical real-insertion-time extension of the actual rational connected
Schwinger function. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
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
    (n : ℕ) (O : Fin n → ℝ → ℝ) :
    (Fin n → ℝ) → ℝ :=
  MGAP4D.ratFinUniformlyExtend n
    (fun time : Fin n → ℚ =>
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O)

/-- Uniform continuity of the rational connected Schwinger data makes the
canonical real insertion-time extension uniformly continuous. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension_uniformContinuous
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
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (huniform : UniformContinuous
      (fun time : Fin n → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O)) :
    UniformContinuous
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
        L n O) := by
  exact MGAP4D.ratFinUniformlyExtend_uniformContinuous n _ huniform

/-- The constructed real insertion-time extension restricts exactly to the
actual rational connected Schwinger function. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension_ratPiCast
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
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (huniform : UniformContinuous
      (fun time : Fin n → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O))
    (time : Fin n → ℚ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
        L n O (MGAP4D.ratPiCast time) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O := by
  exact MGAP4D.ratFinUniformlyExtend_ratPiCast n _ huniform time

/-- Under uniform continuity of the actual rational connected Schwinger function,
the canonically constructed real insertion-time extension is exactly stationary
under every real common translation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_uniformRealInsertion_realShift_eq_self
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
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (huniform : UniformContinuous
      (fun time : Fin n → ℚ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O)) :
    ∀ (time : Fin n → ℝ) (r : ℝ),
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L n O (MGAP4D.realCommonShift time r) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
          L n O time := by
  apply
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realInsertion_realShift_eq_self_of_continuous_extension
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n O
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension
        L n O)
  · exact
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension_uniformContinuous
        L n O huniform).continuous
  · intro time
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalConnectedSchwingerUniformRealInsertionExtension_ratPiCast
        L n O huniform time

end
end MathlibAnalytic
end MGAP4D
