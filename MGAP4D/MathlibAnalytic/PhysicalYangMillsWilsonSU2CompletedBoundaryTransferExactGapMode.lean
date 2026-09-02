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
of the positive-time boundary-pair closure criterion.  Hence a single concrete
completed-boundary-transfer equation at boundary time two is enough to produce
the exact finite Wilson OS time-one eigen-equation.

This theorem removes the abstract post-synthesis closure hypothesis from the
finite common-carrier step without assuming boundary surjectivity or a new
Hilbert-space identification. -/
theorem finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
        (beta n) (hbeta n) f = mu • f)
    (hBoundary :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n)))
    (hTransfer :
      Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
                (beta n) (hbeta n))) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n) f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n))) :
    C.finiteOperator n 1 (A.approximate n psi) =
      mu • A.approximate n psi := by
  have hRange :
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n)) ∈
        Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) :=
    ⟨A.approximate n psi, hBoundary⟩
  have hClosure :
      Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt
        hInvariant C n f := by
    exact
      Q.oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_of_mem_range_and_completedBoundaryTransfer_two
        hInvariant C n
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) 2 f)
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
OS time-one operator when the only post-boundary model input is the concrete
completed-boundary-transfer equation at each cutoff.

The previous closure seam is theoremically reconstructed from `hBoundary` and
`hTransfer`; no sequence or closure witness is exposed to downstream users. -/
theorem physicalOperator_one_apply_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) 2)
    (mu : ℕ → ℝ)
    (muLimit : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hf : ∀ n,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
          (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n)))
    (hTransfer : ∀ n,
      Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 (f n))
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
                (beta n) (hbeta n))) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n) (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n))) :
    T.toPhysicalSemigroup.operator 1 psi = muLimit • psi := by
  apply physicalOperator_one_apply_of_approximating_eigen
    A psi mu muLimit hmu
  intro n
  exact
    finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
      A psi n (f n) (mu n) (hf n) (hBoundary n) (hTransfer n)

/-- Exact-gap specialization with no abstract boundary-pair closure hypothesis.
The sole post-boundary model seam is the genuine completed finite Wilson
boundary transfer equation `K_{n,2} x_n = x_n^(1)` at every cutoff. -/
theorem physicalOperator_one_apply_exactGapClusterContractionRatio_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) 2)
    (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
          (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n)))
    (hTransfer : ∀ n,
      Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 (f n))
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
                (beta n) (hbeta n))) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n) (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n))) :
    T.toPhysicalSemigroup.operator 1 psi =
      exactGapClusterContractionRatio • psi := by
  exact
    physicalOperator_one_apply_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
      A psi f mu exactGapClusterContractionRatio hmu hf hBoundary hTransfer

/-- Construct the exact public gap Hamiltonian mode from the concrete completed
boundary-transfer equation, with the former post-synthesis closure seam fully
eliminated from the statement. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryTransferExactGapTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric : T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (f : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) 2)
    (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
          (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n (psi : P.PhysicalHilbert)) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n)))
    (hTransfer : ∀ n,
      Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 (f n))
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
                (beta n) (hbeta n))) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n) (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
            (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
              (beta n) (hbeta n))) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧
        T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z =
          exactGapValueReal • psi := by
  have hClosure : ∀ n,
      Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt
        hInvariant C n (f n) := by
    intro n
    have hRange :
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) 2 (f n))
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
                (beta n) (hbeta n)) ∈
          Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) :=
      ⟨A.approximate n (psi : P.PhysicalHilbert), hBoundary n⟩
    exact
      Q.oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_of_mem_range_and_completedBoundaryTransfer_two
        hInvariant C n
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) 2 (f n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
          (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
            (beta n) (hbeta n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
            (beta n) (hbeta n) (f n))
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
          (halfExtent n) 2 su2CompletedBoundaryTransferExactGapTwoRankPositive
            (beta n) (hbeta n))
        hRange (hTransfer n)
  exact
    exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
      A hInnerSymmetric hHamiltonianSymmetric psi f mu hmu hf hBoundary hClosure

end SU2CompletedBoundaryTransferExactGap

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
