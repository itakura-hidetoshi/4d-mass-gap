import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTemporalOSComparisonPackage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroDiscreteOSHeatBathComparison

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance temporalOSHeatBathFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance temporalOSHeatBathFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance temporalOSHeatBathFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance temporalOSHeatBathFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance temporalOSHeatBathFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance temporalOSHeatBathFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Structural receipt for the beta-zero canonical boundary heat-bath family
sampled at an arbitrary real spacing.  It records identity, exact natural-time
composition, power realization, and vacuum preservation in one public theorem. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroSampledHeatBathStructuralPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a 0 = 1 ∧
    (∀ m n : ℕ,
      periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a (m + n) =
        periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
            H N hN a m *
          periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
            H N hN a n) ∧
    (∀ n : ℕ,
      periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n =
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a) ^ n) ∧
    (∀ n : ℕ,
      periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n
          (periodicHypercubicEvenBoundaryVacuumL2 H N hN 0 le_rfl) =
        periodicHypercubicEvenBoundaryVacuumL2 H N hN 0 le_rfl) := by
  exact ⟨
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_zero
      H N hN a,
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_add
      H N hN a,
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_eq_pow
      H N hN a,
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_vacuum
      H N hN a⟩

/-- Exact equality branch of the geometric temporal-OS versus beta-zero
heat-bath comparison.  A single zero defect yields one-step intertwining, every
natural-time intertwining, and exact adjoint-compression equality. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroOSTransferHeatBathExactPackage
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (hD :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer = 0) :
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      osTransfer (boundaryToOS f) =
        boundaryToOS
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN 0 le_rfl a f)) ∧
    (∀ n : ℕ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      (osTransfer ^ n) (boundaryToOS f) =
        boundaryToOS
          (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
            H N hN a n f)) ∧
    (∀ n : ℕ,
      realHilbertIsometricAdjointCompression boundaryToOS (osTransfer ^ n) =
        periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n) := by
  exact ⟨
    (periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2_eq_zero_iff
      H N hN a boundaryToOS osTransfer).mp hD,
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransfer_pow_analysis_apply_of_defect_eq_zero
      H N hN a boundaryToOS osTransfer hD,
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransfer_compression_pow_eq_sampled_of_defect_eq_zero
      H N hN a boundaryToOS osTransfer hD⟩

/-- Exact non-equality branch.  A nonzero one-step defect forbids identification
of the complete geometric temporal-OS family with the sampled canonical
heat-bath family through the proposed bridge. -/
theorem
    physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroOSTransferHeatBathNoGoPackage
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ] K)
    (osTransfer : K →L[ℝ] K)
    (hD :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
        H N hN a boundaryToOS osTransfer ≠ 0) :
    ¬ (∀ n : ℕ, ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      (osTransfer ^ n) (boundaryToOS f) =
        boundaryToOS
          (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
            H N hN a n f)) :=
  periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBath_no_go
    H N hN a boundaryToOS osTransfer hD

/-- Terminal classification receipt for the previously reconstructed finite
Wilson random-scan temporal OS transfer.  It is a positive self-adjoint
contraction whose discrete semigroup is exactly its natural powers.  This
receipt does not identify random-scan Markov time with geometric Wilson time. -/
theorem
    finiteWilsonRandomScanTemporalOSTransferClassificationPackage
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    (∀ n : ℕ,
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n =
        L.randomScanTwoSidedIntegerPathOSHilbertShift ^ n) ∧
    (∀ x y : L.RandomScanTwoSidedIntegerPathOSHilbert,
      inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) y =
        inner ℝ x (L.randomScanTwoSidedIntegerPathOSHilbertShift y)) ∧
    (∀ x : L.RandomScanTwoSidedIntegerPathOSHilbert,
      0 ≤ inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) x) ∧
    (∀ x : L.RandomScanTwoSidedIntegerPathOSHilbert,
      ‖L.randomScanTwoSidedIntegerPathOSHilbertShift x‖ ≤ ‖x‖) := by
  rcases L.randomScanTemporalOSTransfer_operator_receipt with
    ⟨hSymm, hPos, hContract⟩
  exact ⟨
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_eq_pow,
    hSymm,
    hPos,
    hContract⟩

/-- Terminal same-carrier comparison dichotomy for the finite Wilson random-scan
OS reconstruction.  Either the candidate equals the one-step OS shift and all
natural-time defects vanish, or a concrete natural-time defect is nonzero. -/
theorem finiteWilsonRandomScanTemporalOSCandidateDichotomyPackage
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShift = candidate ∧
      ∀ n : ℕ,
        L.randomScanTemporalOSSemigroupComparisonDefect candidate n = 0) ∨
    (L.randomScanTwoSidedIntegerPathOSHilbertShift ≠ candidate ∧
      ∃ n : ℕ,
        L.randomScanTemporalOSSemigroupComparisonDefect candidate n ≠ 0) := by
  by_cases hEq : L.randomScanTwoSidedIntegerPathOSHilbertShift = candidate
  · left
    refine ⟨hEq, ?_⟩
    exact
      (L.randomScanTemporalOSSemigroupComparisonDefect_all_eq_zero_iff
        candidate).2 hEq
  · right
    exact ⟨hEq,
      L.randomScanTemporalOSSemigroupComparison_no_go candidate hEq⟩

end

end MathlibAnalytic
end MGAP4D
