import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section

local instance boundaryRawActualAnalysisL2NeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryRawActualAnalysisL2TopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryRawActualAnalysisL2CompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryRawActualAnalysisL2SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryRawActualAnalysisL2MeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryRawActualAnalysisL2BorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryRawActualAnalysisL2SU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryRawActualAnalysisL2HaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance boundaryRawActualAnalysisL2OpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance boundaryRawActualAnalysisL2OpenHalfHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  unfold periodicHypercubicEvenOpenHalfHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
  infer_instance

/-- Continuous-map packaging of the explicit raw actual Wilson analysis
representative. -/
noncomputable def
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ), ℝ) :=
  ⟨periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
      H beta hbeta k c,
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis_continuous
      H beta hbeta k c⟩

/-- The open-half Haar `L²` class of the explicit raw actual Wilson analysis
representative. -/
noncomputable def
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
  ContinuousMap.toLp (E := ℝ) 2
    (periodicHypercubicEvenOpenHalfHaarMeasure H 2) ℝ
    (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
      H beta hbeta k c)

/-- A single point where the continuous raw analysis representative is nonzero
already forces its open-half Haar `L²` class to be nonzero.  Injectivity is the
standard Mathlib `ContinuousMap.toLp_injective` theorem for a measure positive
on nonempty open sets. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_ne_zero_of_point_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hx : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
      H beta hbeta k c x ≠ 0) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      H beta hbeta k c ≠ 0 := by
  let f :=
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
      H beta hbeta k c
  have hf : f ≠ 0 := by
    intro h0
    apply hx
    have hx0 := congrArg
      (fun g : C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ), ℝ) => g x) h0
    simpa [f,
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap]
      using hx0
  intro hL2
  apply hf
  apply ContinuousMap.toLp_injective
    (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
  simpa [f,
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2] using hL2

/-- Every nonzero normalized-trace polynomial therefore produces a
positive-degree witness whose explicit actual Wilson analysis representative is
nonzero as an open-half Haar `L²` vector. -/
theorem
    periodicHypercubicEvenNormalizedTracePolynomial_exists_positiveDegree_rawActualAnalysisHaarL2_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0) :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta.le k c ≠ 0 := by
  rcases
    periodicHypercubicEvenNormalizedTracePolynomial_exists_positiveDegree_rawActualAnalysis_fourCompanionSection_ne_zero
      H hH beta hbeta k c hc with
    ⟨i, hi, d, hd⟩
  refine ⟨i, hi, ?_⟩
  exact
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_ne_zero_of_point_ne_zero
      H beta hbeta.le k c
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H (Nat.zero_lt_of_lt hH)
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d))
      hd

end

end MathlibAnalytic
end MGAP4D
