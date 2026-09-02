import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferExactGapMode
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryTransferSpatialSlicePair
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

local instance completedBoundaryOneSlabSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundaryOneSlabTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundaryOneSlabCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundaryOneSlabSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundaryOneSlabMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundaryOneSlabBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance completedBoundaryOneSlabSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Pair-coordinate form of the missing lattice/OS compatibility at one cutoff.

The completed Wilson OS boundary transfer at boundary time two is conjugated to
ordered primary/antipodal spatial-slice coordinates.  The requirement says that
on every gauge-invariant external tensor it acts by one normalized physical
one-slab transfer on each endpoint.

This is deliberately stronger and more structural than a mode-by-mode boundary
equation.  It is the operator-facing identity that the finite one-slab Wilson
kernel must eventually prove. -/
def CompletedBoundaryTransferOneSlabPairIntertwiningAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) : Prop :=
  ∀ f omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N,
    periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
        (halfExtent n) N
        (Q.completedBoundaryTransfer hInvariant C n 2)
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N omega)) =
      periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
        (halfExtent n) N
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) omega)

/-- Pair-coordinate one-slab compatibility immediately gives the corresponding
shared-boundary equality for every pair of gauge-invariant endpoint vectors.

The proof uses only the exact inverse boundary/pair Haar-`L²` coordinate
isometries.  No finite OS eigen-equation, continuum equation, or Hamiltonian
equation enters. -/
theorem completedBoundaryTransfer_two_oneSidedBoundary_of_oneSlabPairIntertwiningAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (hPair : CompletedBoundaryTransferOneSlabPairIntertwiningAt
      Q hInvariant C n)
    (f omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N) :
    Q.completedBoundaryTransfer hInvariant C n 2
        (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N omega)) =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) N
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) omega) := by
  let xPair :=
    periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
      (halfExtent n) N
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
        (halfExtent n) N f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
        (halfExtent n) N omega)
  let xPairOne :=
    periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
      (halfExtent n) N
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        (halfExtent n) N hN (beta n) (hbeta n) f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        (halfExtent n) N hN (beta n) (hbeta n) omega)
  have hForward :
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N omega)) =
        xPair := by
    simpa [periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2, xPair] using
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePair_rightInverse
        (halfExtent n) N xPair
  have hPairApply :
      periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2) xPair =
        xPairOne := by
    unfold CompletedBoundaryTransferOneSlabPairIntertwiningAt at hPair
    simpa [xPair, xPairOne] using hPair f omega
  calc
    Q.completedBoundaryTransfer hInvariant C n 2
        (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N omega)) =
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) N
        (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2)
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
              (halfExtent n) N
              (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
                (halfExtent n) N f)
              (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
                (halfExtent n) N omega)))) := by
      symm
      exact periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_recover
        (halfExtent n) N
        (Q.completedBoundaryTransfer hInvariant C n 2)
        (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N omega))
    _ = periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) N
        (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2) xPair) := by
      rw [hForward]
    _ = periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) N xPairOne := by
      rw [hPairApply]
    _ = periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) N
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) omega) := by
      rfl

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

private theorem su2CompletedBoundaryOneSlabRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- Public SU(2) one-sided boundary vector used by the completed-transfer lane. -/
abbrev su2CompletedBoundaryOneSlabModeBoundary
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2 H 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H 2 f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      H 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta)

/-- Public SU(2) one-step boundary vector for the same mode. -/
abbrev su2CompletedBoundaryOneSlabModeBoundaryOneStep
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2 H 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      H 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      H 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta)

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

section SU2CompletedBoundaryOneSlabIntertwining

variable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant C}

/-- The structural pair-coordinate compatibility generates the exact SU(2)
physical-mode boundary-transfer equation required by the previous closure-free
exact-gap theorem. -/
theorem completedBoundaryTransfer_two_physicalModeBoundary_of_oneSlabPairIntertwiningAt
    (n : ℕ)
    (hPair :
      PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairIntertwiningAt
        Q hInvariant C n)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) :
    Q.completedBoundaryTransfer hInvariant C n 2
        (su2CompletedBoundaryOneSlabModeBoundary
          (halfExtent n) (beta n) (hbeta n) f) =
      su2CompletedBoundaryOneSlabModeBoundaryOneStep
        (halfExtent n) (beta n) (hbeta n) f := by
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      (halfExtent n) 2 su2CompletedBoundaryOneSlabRankPositive
        (beta n) (hbeta n)
  have h :=
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.completedBoundaryTransfer_two_oneSidedBoundary_of_oneSlabPairIntertwiningAt
      Q hInvariant C n hPair f omega
  simpa [su2CompletedBoundaryOneSlabModeBoundary,
    su2CompletedBoundaryOneSlabModeBoundaryOneStep,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalModeLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp,
    omega] using h

/-- At one cutoff, structural pair-coordinate one-slab compatibility replaces
the former mode-specific completed-boundary equation and yields the exact finite
Wilson OS time-one eigen-equation. -/
theorem finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeOneSlabPairIntertwining
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert) (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryOneSlabRankPositive
        (beta n) (hbeta n) f = mu • f)
    (hBoundary : Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) f)
    (hPair :
      PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairIntertwiningAt
        Q hInvariant C n) :
    C.finiteOperator n 1 (A.approximate n psi) = mu • A.approximate n psi := by
  apply finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    A psi n f mu hf hBoundary
  exact completedBoundaryTransfer_two_physicalModeBoundary_of_oneSlabPairIntertwiningAt
    n hPair f

/-- A cutoff family of pair-coordinate one-slab intertwining identities removes
the mode-specific `hTransfer` family from the finite-to-continuum eigenmode
statement. -/
theorem physicalOperator_one_apply_of_normalizedPhysicalTransferModeOneSlabPairIntertwining
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ) (muLimit : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryOneSlabRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hPair : ∀ n,
      PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairIntertwiningAt
        Q hInvariant C n) :
    T.toPhysicalSemigroup.operator 1 psi = muLimit • psi := by
  apply physicalOperator_one_apply_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    A psi f mu muLimit hmu hf hBoundary
  intro n
  exact completedBoundaryTransfer_two_physicalModeBoundary_of_oneSlabPairIntertwiningAt
    n (hPair n) (f n)

/-- Exact-gap continuum specialization whose only post-boundary input is the
structural pair-coordinate one-slab intertwining family. -/
theorem physicalOperator_one_apply_exactGapClusterContractionRatio_of_normalizedPhysicalTransferModeOneSlabPairIntertwining
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryOneSlabRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hPair : ∀ n,
      PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairIntertwiningAt
        Q hInvariant C n) :
    T.toPhysicalSemigroup.operator 1 psi = exactGapClusterContractionRatio • psi := by
  exact physicalOperator_one_apply_of_normalizedPhysicalTransferModeOneSlabPairIntertwining
    A psi f mu exactGapClusterContractionRatio hmu hf hBoundary hPair

/-- The exact public Hamiltonian mode now depends on one structural one-slab
pair-intertwining family rather than on a separate completed-boundary equation
for every chosen physical mode. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeOneSlabPairIntertwining
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryOneSlabRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric : T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryOneSlabRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n (psi : P.PhysicalHilbert)) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hPair : ∀ n,
      PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairIntertwiningAt
        Q hInvariant C n) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧
        T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z =
          exactGapValueReal • psi := by
  apply exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    A hInnerSymmetric hHamiltonianSymmetric psi f mu hmu hf hBoundary
  intro n
  exact completedBoundaryTransfer_two_physicalModeBoundary_of_oneSlabPairIntertwiningAt
    n (hPair n) (f n)

end SU2CompletedBoundaryOneSlabIntertwining

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D