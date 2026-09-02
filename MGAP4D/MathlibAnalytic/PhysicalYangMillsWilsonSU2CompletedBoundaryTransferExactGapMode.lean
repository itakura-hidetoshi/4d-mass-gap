import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2BoundaryPairClosureExactGapMode
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2BoundaryPairCompletedTransferCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

private theorem su2CompletedBoundaryTransferExactGapTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance su2CompletedBoundaryTransferExactGapSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance su2CompletedBoundaryTransferExactGapTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2CompletedBoundaryTransferExactGapCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2CompletedBoundaryTransferExactGapSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2CompletedBoundaryTransferExactGapMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2CompletedBoundaryTransferExactGapBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private abbrev su2CompletedBoundaryTransferModeBoundary
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2 H 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H 2 f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      H 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta)

private abbrev su2CompletedBoundaryTransferModeBoundaryOneStep
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2 H 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      H 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      H 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta)

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

section SU2CompletedBoundaryTransferExactGap

variable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant C}

/-- The common-carrier boundary identification already supplies the range part
of the positive-time boundary-pair closure criterion. Hence one concrete
completed-boundary-transfer equation at boundary time two produces the exact
finite Wilson OS time-one eigen-equation. -/
theorem finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert) (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
        (beta n) (hbeta n) f = mu • f)
    (hBoundary : Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryTransferModeBoundary
        (halfExtent n) (beta n) (hbeta n) f)
    (hTransfer : Q.completedBoundaryTransfer hInvariant C n 2
      (su2CompletedBoundaryTransferModeBoundary (halfExtent n) (beta n) (hbeta n) f) =
      su2CompletedBoundaryTransferModeBoundaryOneStep (halfExtent n) (beta n) (hbeta n) f) :
    C.finiteOperator n 1 (A.approximate n psi) = mu • A.approximate n psi := by
  have hRange :
      su2CompletedBoundaryTransferModeBoundary (halfExtent n) (beta n) (hbeta n) f ∈
        Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) :=
    ⟨A.approximate n psi, hBoundary⟩
  have hClosure :
      Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt
        hInvariant C n f := by
    exact
      Q.oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_of_mem_range_and_completedBoundaryTransfer_two
        hInvariant C n
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp (halfExtent n) 2 f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
          (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
            (beta n) (hbeta n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
            (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
          (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
            (beta n) (hbeta n))
        hRange hTransfer
  exact
    finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
      A psi n f mu hf hBoundary hClosure

/-- Cutoff-dependent SU(2) one-slice transfer eigenmodes reach the continuum
OS time-one operator with the concrete completed-boundary-transfer equation as
the only post-boundary model input. -/
theorem physicalOperator_one_apply_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ) (muLimit : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryTransferModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hTransfer : ∀ n, Q.completedBoundaryTransfer hInvariant C n 2
      (su2CompletedBoundaryTransferModeBoundary (halfExtent n) (beta n) (hbeta n) (f n)) =
      su2CompletedBoundaryTransferModeBoundaryOneStep (halfExtent n) (beta n) (hbeta n) (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = muLimit • psi := by
  apply physicalOperator_one_apply_of_approximating_eigen A psi mu muLimit hmu
  intro n
  exact
    finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
      A psi n (f n) (mu n) (hf n) (hBoundary n) (hTransfer n)

/-- Exact-gap specialization with no abstract boundary-pair closure hypothesis.
The sole post-boundary seam is `K_{n,2} x_n = x_n^(1)` at every cutoff. -/
theorem physicalOperator_one_apply_exactGapClusterContractionRatio_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryTransferModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hTransfer : ∀ n, Q.completedBoundaryTransfer hInvariant C n 2
      (su2CompletedBoundaryTransferModeBoundary (halfExtent n) (beta n) (hbeta n) (f n)) =
      su2CompletedBoundaryTransferModeBoundaryOneStep (halfExtent n) (beta n) (hbeta n) (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = exactGapClusterContractionRatio • psi := by
  exact
    physicalOperator_one_apply_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
      A psi f mu exactGapClusterContractionRatio hmu hf hBoundary hTransfer

/-- Construct the exact public gap Hamiltonian mode from the concrete completed
boundary-transfer equation, with the former closure seam absent from the
statement. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric : T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n (psi : P.PhysicalHilbert)) = su2CompletedBoundaryTransferModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hTransfer : ∀ n, Q.completedBoundaryTransfer hInvariant C n 2
      (su2CompletedBoundaryTransferModeBoundary (halfExtent n) (beta n) (hbeta n) (f n)) =
      su2CompletedBoundaryTransferModeBoundaryOneStep (halfExtent n) (beta n) (hbeta n) (f n)) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧
        T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z =
          exactGapValueReal • psi := by
  obtain ⟨z, hz, hEigen⟩ :=
    exists_vacuumOrthogonalClosedRightHamiltonian_mode_of_approximating_eigen
      A hInnerSymmetric hHamiltonianSymmetric psi mu exactGapClusterContractionRatio
        exact_gap_cluster_contraction_ratio_pos hmu (fun n =>
          finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
            A (psi : P.PhysicalHilbert) n (f n) (mu n)
              (hf n) (hBoundary n) (hTransfer n))
  refine ⟨z, hz, ?_⟩
  rw [neg_log_exactGapClusterContractionRatio] at hEigen
  exact hEigen

end SU2CompletedBoundaryTransferExactGap

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
