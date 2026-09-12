import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance geometricOSIdentityFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance geometricOSIdentityFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance geometricOSIdentityFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance geometricOSIdentityFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance geometricOSIdentityFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance geometricOSIdentityFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Simultaneous realization predicate for the current geometric one-layer OS
form and a sampled canonical beta-zero heat-bath step. -/
def FiniteWilsonGeometricOSOneLayerAndHeatBathRealization
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert) : Prop :=
  (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
    finiteWilsonOSOneLayerOperatorMatrixDefect
      P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0) ∧
  periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
    H N hN a boundaryToGeometricOS candidate = 0

/-- Exact classification of simultaneous realizations.  The current Wilson
one-layer form and the sampled beta-zero heat-bath step can be realized by one
bounded operator through the chosen bridge if and only if the candidate is the
identity and the heat-bath step is itself identity. -/
theorem finiteWilsonGeometricOSOneLayerAndHeatBathRealization_iff
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert) :
    FiniteWilsonGeometricOSOneLayerAndHeatBathRealization
        P H N hN a boundaryToGeometricOS candidate ↔
      candidate = P.oneLayerIdentityTransfer ∧
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a = 1 := by
  constructor
  · rintro ⟨hMatrix, hBridge⟩
    have hCandidate :=
      P.oneLayerOperator_eq_identityTransfer_of_matrixDefect_eq_zero
        candidate hMatrix
    refine ⟨hCandidate, ?_⟩
    rw [hCandidate] at hBridge
    apply
      (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
        P H N hN a boundaryToGeometricOS).mp
    simpa [
      periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2]
      using hBridge
  · rintro ⟨hCandidate, hHeatBath⟩
    constructor
    · intro F G
      rw [hCandidate]
      exact P.oneLayerIdentityTransfer_matrixDefect_eq_zero F G
    · rw [hCandidate]
      have hIdentityDefect :
          periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
            P H N hN a boundaryToGeometricOS = 0 :=
        (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
          P H N hN a boundaryToGeometricOS).2 hHeatBath
      simpa [
        periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2]
        using hIdentityDefect

/-- A nonidentity heat-bath step gives an exact no-go theorem for simultaneous
realization by any bounded operator reproducing the current Wilson one-layer
form. -/
theorem finiteWilsonGeometricOSOneLayerAndHeatBathRealization_no_go
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert)
    (hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a ≠ 1) :
    ¬ FiniteWilsonGeometricOSOneLayerAndHeatBathRealization
        P H N hN a boundaryToGeometricOS candidate := by
  intro hRealization
  apply hHeatBath
  exact
    (finiteWilsonGeometricOSOneLayerAndHeatBathRealization_iff
      P H N hN a boundaryToGeometricOS candidate).mp hRealization |>.2

/-- Complete terminal trichotomy for an arbitrary candidate operator.  Either
it fails at a geometric Wilson matrix element, or the sampled heat-bath step is
identity, or its boundary bridge defect is nonzero. -/
theorem finiteWilsonGeometricOSOneLayerAndHeatBath_terminal_trichotomy
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert) :
    (∃ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        P.reflectionData P.oneLayerObservableEmbedding candidate F G ≠ 0) ∨
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a = 1 ∨
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToGeometricOS candidate ≠ 0 := by
  classical
  by_cases hMatrix :
      ∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
        finiteWilsonOSOneLayerOperatorMatrixDefect
          P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0
  · have hCandidate :=
      P.oneLayerOperator_eq_identityTransfer_of_matrixDefect_eq_zero
        candidate hMatrix
    by_cases hHeatBath :
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a = 1
    · exact Or.inr (Or.inl hHeatBath)
    · right
      right
      rw [hCandidate]
      have hIdentityDefect :=
        periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_ne_zero_of_heatBath_ne_one
          P H N hN a boundaryToGeometricOS hHeatBath
      simpa [
        periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2]
        using hIdentityDefect
  · left
    push_neg at hMatrix
    exact hMatrix

/-- Public terminal package.  It records the exact Hilbert completion, the
identity uniqueness theorem, and the complete comparison classification without
promoting the reflection form to a nontrivial Euclidean-time transfer. -/
theorem physicalYangMillsGaugeInvariantGeometricOSHilbertIdentityObstructionFinalPackage
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    DenseRange P.oneLayerObservableEmbedding ∧
    (∀ candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert,
      (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
        finiteWilsonOSOneLayerOperatorMatrixDefect
          P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0) ↔
        candidate = P.oneLayerIdentityTransfer) ∧
    (∀ candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert,
      FiniteWilsonGeometricOSOneLayerAndHeatBathRealization
          P H N hN a boundaryToGeometricOS candidate ↔
        candidate = P.oneLayerIdentityTransfer ∧
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a = 1) := by
  exact ⟨P.oneLayerObservableEmbedding_denseRange,
    P.oneLayerOperator_all_matrixDefects_eq_zero_iff,
    finiteWilsonGeometricOSOneLayerAndHeatBathRealization_iff
      P H N hN a boundaryToGeometricOS⟩

end

end MathlibAnalytic
end MGAP4D
