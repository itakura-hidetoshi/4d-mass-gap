import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryVacuumAdjoint
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredHeatBathEvolutionL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance canonicalBoundaryZeroTimeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryZeroTimeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryZeroTimeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryZeroTimeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryZeroTimeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryZeroTimeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A boundary vector orthogonal to the concrete OS boundary vacuum is sent by
canonical analysis to a vector orthogonal to the actual finite Gibbs vacuum. -/
theorem periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_centered
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2
        H N hN beta hbeta) f = 0) :
    inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsVacuumL2
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta f) = 0 := by
  rw [periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum_inner]
  exact hf

/-- At zero time, the actual centered heat-bath evolution, canonical analysis,
and adjoint synthesis return every boundary-vacuum-orthogonal vector exactly.

Thus the zero-time part of boundary-moment intertwining is theorem-generated;
only positive-time dynamical compatibility remains model-specific. -/
theorem periodicHypercubicEvenCanonicalBoundary_centeredHeatBath_zero_roundTrip
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2
        H N hN beta hbeta) f = 0) :
    periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          0
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) = f := by
  let W := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  have hcentered : inner ℝ W.gibbsVacuumL2
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta f) = 0 :=
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_centered
      H N hN beta hbeta f hf
  rw [continuous_compact_oriented_centeredHeatBathEvolutionL2_zero]
  rw [continuous_compact_oriented_vacuumCenteringL2_apply_of_orthogonal
    W _ hcentered]
  exact periodicHypercubicEvenCanonicalBoundarySynthesisL2_analysis
    H N hN beta hbeta f

end

end MathlibAnalytic
end MGAP4D