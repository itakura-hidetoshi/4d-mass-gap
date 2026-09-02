import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabMatrixCoefficient
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

local instance completedBoundaryPhysicalModeMatrixCoefficientSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundaryPhysicalModeMatrixCoefficientTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundaryPhysicalModeMatrixCoefficientCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundaryPhysicalModeMatrixCoefficientSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundaryPhysicalModeMatrixCoefficientMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundaryPhysicalModeMatrixCoefficientBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance completedBoundaryPhysicalModeMatrixCoefficientSpatialLinkFintype (H : ℕ) :
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

/-- Pointwise weak one-slab compatibility for one selected pair of endpoint
vectors at one cutoff.

Unlike `CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt`, this does not
quantify over every gauge-invariant input pair.  It asks only for equality of
all pair-Haar matrix coefficients for the single pair `(f, omega)`.  This is
the smallest Hilbert-space statement needed to recover the corresponding
shared-boundary transfer identity. -/
def CompletedBoundaryTransferOneSlabPairWeakAtFor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N) : Prop :=
  ∀ z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N,
    inner ℝ
        (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2)
          (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N omega))) z =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            (halfExtent n) N hN (beta n) (hbeta n) f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            (halfExtent n) N hN (beta n) (hbeta n) omega)) z

/-- The all-input weak intertwining from the previous unit specializes to the
pointwise weak compatibility for any chosen endpoint pair. -/
theorem completedBoundaryTransferOneSlabPairWeakAtFor_of_weakIntertwiningAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (hWeak : CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt
      Q hInvariant C n)
    (f omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N) :
    CompletedBoundaryTransferOneSlabPairWeakAtFor
      Q hInvariant C n f omega := by
  intro z
  exact hWeak f omega z

/-- Pointwise equality of all real matrix coefficients recovers the exact
shared-boundary one-slab identity for that single endpoint pair.

The first step is Hilbert separation on pair Haar `L²`.  The second step uses
only the already-canonical exact inverse boundary/pair `L²` coordinate
isometries.  No eigen-equation or continuum input is used. -/
theorem completedBoundaryTransfer_two_oneSidedBoundary_of_oneSlabPairWeakAtFor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N)
    (hWeak : CompletedBoundaryTransferOneSlabPairWeakAtFor
      Q hInvariant C n f omega) :
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
  let xPair : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
    periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
      (halfExtent n) N
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
        (halfExtent n) N f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
        (halfExtent n) N omega)
  let x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
    periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
      (halfExtent n) N
      (Q.completedBoundaryTransfer hInvariant C n 2) xPair
  let y : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N :=
    periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
      (halfExtent n) N
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        (halfExtent n) N hN (beta n) (hbeta n) f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        (halfExtent n) N hN (beta n) (hbeta n) omega)
  have hxy : ∀ z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N, inner ℝ x z = inner ℝ y z := by
    intro z
    simpa [CompletedBoundaryTransferOneSlabPairWeakAtFor, xPair, x, y] using hWeak z
  have htest := hxy (x - y)
  have hself : inner ℝ (x - y) (x - y) = 0 := by
    calc
      inner ℝ (x - y) (x - y) =
          inner ℝ x (x - y) - inner ℝ y (x - y) := by
        rw [inner_sub_left]
      _ = 0 := by rw [htest]; ring
  have hnormsq : ‖x - y‖ ^ 2 = 0 := by
    simpa using hself
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  have hPairApply : x = y := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
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
        (halfExtent n) N x := by
      rw [hForward]
    _ = periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) N y := by
      rw [hPairApply]
    _ = periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) N
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
          (halfExtent n) N hN (beta n) (hbeta n) omega) := by
      rfl

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

private theorem su2CompletedBoundaryPhysicalModeMatrixRankPositive : 0 < (2 : ℕ) := by
  norm_num

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

section SU2CompletedBoundaryPhysicalModeMatrixCoefficient

variable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant C}

/-- The exact-gap lane only needs weak matrix coefficients for the selected
physical mode paired with the normalized one-slab top mode, not an operator
identity on every gauge-invariant endpoint pair. -/
def SU2CompletedBoundaryTransferPhysicalModeWeakAt
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) : Prop :=
  PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairWeakAtFor
    Q hInvariant C n f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        (halfExtent n) 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive
          (beta n) (hbeta n))

/-- Mode-specific weak matrix coefficients recover exactly the completed
boundary equation consumed by the finite OS eigenmode theorem. -/
theorem completedBoundaryTransfer_two_physicalModeBoundary_of_weakMatrixCoefficients
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2)
    (hWeak : SU2CompletedBoundaryTransferPhysicalModeWeakAt
      (Q := Q) (hInvariant := hInvariant) (C := C) n f) :
    Q.completedBoundaryTransfer hInvariant C n 2
        (su2CompletedBoundaryOneSlabModeBoundary
          (halfExtent n) (beta n) (hbeta n) f) =
      su2CompletedBoundaryOneSlabModeBoundaryOneStep
        (halfExtent n) (beta n) (hbeta n) f := by
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      (halfExtent n) 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive
        (beta n) (hbeta n)
  have h :=
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.completedBoundaryTransfer_two_oneSidedBoundary_of_oneSlabPairWeakAtFor
      Q hInvariant C n f omega hWeak
  simpa [SU2CompletedBoundaryTransferPhysicalModeWeakAt,
    su2CompletedBoundaryOneSlabModeBoundary,
    su2CompletedBoundaryOneSlabModeBoundaryOneStep,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalModeLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp,
    omega] using h

/-- At one cutoff, the scalar weak matrix-coefficient identity for the selected
physical mode and top mode already gives the exact finite OS time-one
eigen-equation. -/
theorem finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert) (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive
        (beta n) (hbeta n) f = mu • f)
    (hBoundary : Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) f)
    (hWeak : SU2CompletedBoundaryTransferPhysicalModeWeakAt
      (Q := Q) (hInvariant := hInvariant) (C := C) n f) :
    C.finiteOperator n 1 (A.approximate n psi) = mu • A.approximate n psi := by
  apply finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    A psi n f mu hf hBoundary
  exact completedBoundaryTransfer_two_physicalModeBoundary_of_weakMatrixCoefficients
    n f hWeak

/-- A cutoff family of mode-specific scalar matrix-coefficient identities is
enough for the continuum OS time-one eigenmode. -/
theorem physicalOperator_one_apply_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ) (muLimit : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hWeak : ∀ n, SU2CompletedBoundaryTransferPhysicalModeWeakAt
      (Q := Q) (hInvariant := hInvariant) (C := C) n (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = muLimit • psi := by
  apply physicalOperator_one_apply_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    A psi f mu muLimit hmu hf hBoundary
  intro n
  exact completedBoundaryTransfer_two_physicalModeBoundary_of_weakMatrixCoefficients
    n (f n) (hWeak n)

/-- Exact-gap continuum specialization with only the selected physical-mode
weak Wilson matrix coefficients as post-boundary input. -/
theorem physicalOperator_one_apply_exactGapClusterContractionRatio_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hWeak : ∀ n, SU2CompletedBoundaryTransferPhysicalModeWeakAt
      (Q := Q) (hInvariant := hInvariant) (C := C) n (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = exactGapClusterContractionRatio • psi := by
  exact physicalOperator_one_apply_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    A psi f mu exactGapClusterContractionRatio hmu hf hBoundary hWeak

/-- The exact public Hamiltonian mode now needs only the scalar pair-Haar matrix
coefficients for the selected physical mode and the transfer-fixed top mode at
each cutoff.  No all-input pair intertwining hypothesis remains in this wrapper. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric : T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2CompletedBoundaryPhysicalModeMatrixRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n (psi : P.PhysicalHilbert)) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hWeak : ∀ n, SU2CompletedBoundaryTransferPhysicalModeWeakAt
      (Q := Q) (hInvariant := hInvariant) (C := C) n (f n)) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧
        T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z =
          exactGapValueReal • psi := by
  apply exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeCompletedBoundaryTransfer
    A hInnerSymmetric hHamiltonianSymmetric psi f mu hmu hf hBoundary
  intro n
  exact completedBoundaryTransfer_two_physicalModeBoundary_of_weakMatrixCoefficients
    n (f n) (hWeak n)

end SU2CompletedBoundaryPhysicalModeMatrixCoefficient

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
