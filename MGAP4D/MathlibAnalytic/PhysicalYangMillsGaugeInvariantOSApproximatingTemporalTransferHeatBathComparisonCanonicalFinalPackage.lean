import MGAP4D.MathlibAnalytic.FiniteWilsonOSOneLayerTransferFormPackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingTemporalTransferHeatBathComparisonFinalPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance temporalOSTwoDefectFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance temporalOSTwoDefectFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance temporalOSTwoDefectFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance temporalOSTwoDefectFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance temporalOSTwoDefectFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance temporalOSTwoDefectFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Complete exact branch for the two independent identifications required to
compare geometric Wilson Euclidean time with beta-zero canonical heat-bath
time.

The first zero-defect family says that `osTransfer` realizes every matrix
element of the actual reflected one-layer Wilson kernel on the supplied
observable image.  The second zero defect says that the same operator
intertwines the canonical boundary heat-bath one-step sample through an explicit
Hilbert isometry.  Only when both statements hold do the geometric one-layer
form and every sampled heat-bath time belong to one exact operator package. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingTemporalTransferHeatBathTwoDefectExactPackage
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (hMatrix : ∀ F G : R.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding osTransfer F G = 0)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0) :
    (∀ F G : R.PositiveConfiguration → ℝ,
      inner ℝ (osTransfer (observableEmbedding F)) (observableEmbedding G) =
        R.wilsonOneLayerTransferForm F G) ∧
    (∀ F G : R.PositiveConfiguration → ℝ,
      inner ℝ (osTransfer (observableEmbedding F)) (observableEmbedding G) =
        inner ℝ (observableEmbedding F)
          (osTransfer (observableEmbedding G))) ∧
    (∀ F : R.PositiveConfiguration → ℝ,
      0 ≤ inner ℝ
        (osTransfer (observableEmbedding F)) (observableEmbedding F)) ∧
    (∀ n : ℕ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      (osTransfer ^ n) (boundaryToOS f) =
        boundaryToOS
          (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
            H N hN a n f)) ∧
    (∀ n : ℕ,
      realHilbertIsometricAdjointCompression boundaryToOS (osTransfer ^ n) =
        periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n) := by
  have hMatrixElements :
      ∀ F G : R.PositiveConfiguration → ℝ,
        inner ℝ (osTransfer (observableEmbedding F)) (observableEmbedding G) =
          R.wilsonOneLayerTransferForm F G := by
    intro F G
    exact
      (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
        R observableEmbedding osTransfer F G).mp (hMatrix F G)
  have hSymmetric :
      ∀ F G : R.PositiveConfiguration → ℝ,
        inner ℝ (osTransfer (observableEmbedding F)) (observableEmbedding G) =
          inner ℝ (observableEmbedding F)
            (osTransfer (observableEmbedding G)) :=
    finiteWilsonOSOneLayerOperator_symmetric_on_range_of_matrixDefect_eq_zero
      R observableEmbedding osTransfer hMatrix
  have hPositive :
      ∀ F : R.PositiveConfiguration → ℝ,
        0 ≤ inner ℝ
          (osTransfer (observableEmbedding F)) (observableEmbedding F) :=
    finiteWilsonOSOneLayerOperator_nonneg_on_range_of_matrixDefect_eq_zero
      R B observableEmbedding osTransfer hMatrix
  rcases
      physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroOSTransferHeatBathExactPackage
        H N hN a boundaryToOS osTransfer hHeatBath with
    ⟨_hOne, hAllTimes, hCompression⟩
  exact ⟨hMatrixElements, hSymmetric, hPositive, hAllTimes, hCompression⟩

/-- Complete no-go branch for the two-defect comparison.  A witness in either
layer is sufficient: a nonzero Wilson matrix-element defect rules out geometric
one-layer realization, while a nonzero boundary/heat-bath defect rules out the
all-natural-time intertwining. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingTemporalTransferHeatBathTwoDefectNoGoPackage
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (obstruction :
      (∃ F G : R.PositiveConfiguration → ℝ,
        finiteWilsonOSOneLayerOperatorMatrixDefect
          R observableEmbedding osTransfer F G ≠ 0) ∨
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer ≠ 0) :
    ¬ ((∀ F G : R.PositiveConfiguration → ℝ,
      inner ℝ (osTransfer (observableEmbedding F)) (observableEmbedding G) =
        R.wilsonOneLayerTransferForm F G) ∧
      (∀ n : ℕ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        (osTransfer ^ n) (boundaryToOS f) =
          boundaryToOS
            (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
              H N hN a n f))) := by
  intro hBoth
  rcases hBoth with ⟨hMatrix, hAllTimes⟩
  rcases obstruction with hMatrixObstacle | hHeatBathObstacle
  · rcases hMatrixObstacle with ⟨F, G, hFG⟩
    exact
      (finiteWilsonOSOneLayerOperatorMatrixDefect_no_go
        R observableEmbedding osTransfer F G hFG) hMatrix
  · exact
      (periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBath_no_go
        H N hN a boundaryToOS osTransfer hHeatBathObstacle) hAllTimes

/-- Canonical terminal dichotomy.  The exact comparison is controlled by two
independent defects and cannot be collapsed to a name-based identification of
random-scan, geometric Wilson, and heat-bath time. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingTemporalTransferHeatBathTwoDefectDichotomy
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (observableEmbedding :
      (R.PositiveConfiguration → ℝ) →ₗ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K) :
    ((∀ F G : R.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding osTransfer F G = 0) ∧
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0) ∨
    ((∃ F G : R.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding osTransfer F G ≠ 0) ∨
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer ≠ 0) := by
  by_cases hMatrix : ∀ F G : R.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        R observableEmbedding osTransfer F G = 0
  · by_cases hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0
    · exact Or.inl ⟨hMatrix, hHeatBath⟩
    · exact Or.inr (Or.inr hHeatBath)
  · right
    left
    push_neg at hMatrix
    exact hMatrix

end

end MathlibAnalytic
end MGAP4D
