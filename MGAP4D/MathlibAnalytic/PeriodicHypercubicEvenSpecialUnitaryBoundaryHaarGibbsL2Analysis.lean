import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHaarGibbsL2Isometry
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryHaarL2Analysis
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance periodicBoundaryAnalysisNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance periodicBoundaryAnalysisTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance periodicBoundaryAnalysisCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance periodicBoundaryAnalysisSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance periodicBoundaryAnalysisMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance periodicBoundaryAnalysisBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical finite periodic Wilson boundary-analysis map.

A boundary Haar `L²` vector is first pulled back to the full configuration
Haar space along the genuine reflection-fixed boundary projection.  It is then
transported to the Wilson Gibbs `L²` space by multiplication with the inverse
square root of the normalized Gibbs density.  Both stages are linear
isometries, hence so is their composition. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H)
          N hN beta hbeta).gibbsMeasure :=
  let W := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  W.haarToGibbsL2Isometry.comp
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryHaarL2Analysis
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- The canonical boundary-analysis map preserves the boundary Haar `L²`
norm exactly. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis_norm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
        H N hN beta hbeta f‖ = ‖f‖ :=
  (periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
    H N hN beta hbeta).norm_map f

end

end MathlibAnalytic
end MGAP4D
