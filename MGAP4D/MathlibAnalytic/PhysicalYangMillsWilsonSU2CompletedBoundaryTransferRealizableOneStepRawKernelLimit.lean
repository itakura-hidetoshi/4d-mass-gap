import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferProjectedSynthesisDensity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferPhysicalModeRawKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

local instance realizableRawKernelLimitSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩
local instance realizableRawKernelLimitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance realizableRawKernelLimitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance realizableRawKernelLimitSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance realizableRawKernelLimitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance realizableRawKernelLimitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance realizableRawKernelLimitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- The selected endpoint pair before one finite Wilson time step. -/
noncomputable def physicalTopPairInput
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent n) N :=
  periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
    (halfExtent n) N
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp (halfExtent n) N f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) N hN (beta n) (hbeta n))

/-- Literal normalized one-slab Wilson coefficient for the selected physical
mode, the top endpoint mode, and an arbitrary pair-Haar test kernel. -/
noncomputable def physicalTopRawKernelCoefficient
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)‖⁻¹ *
    realL2HilbertSchmidtKernelPairing z
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
          (halfExtent n) N f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
        (halfExtent n) N hN (beta n) (hbeta n))

/-- Minimal remaining finite-model closure/Fubini seam for the selected pair.

Take any sequence of actual OS carriers whose completed physical states tend to
the orthogonal projection of the selected endpoint pair into the completed OS
boundary image. After one realizable integer lattice step, actual Wilson
adjoint synthesis is required to have pair-Haar coefficient tending to the
literal normalized one-slab Wilson kernel coefficient.

This statement contains no abstract common-semigroup translation, no finite or
continuum eigen-equation, and no Hamiltonian input. -/
def RealizableOneStepPhysicalTopRawKernelLimitAtFor
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N) : Prop :=
  ∀ z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N,
    ∀ F : ℕ →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      Tendsto
          (fun k =>
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
              (F k))
          atTop
          (𝓝 (Q.completedBoundaryProjectedPhysicalState hInvariant n
            (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
              (halfExtent n) N (physicalTopPairInput n f)))) →
        Tendsto
          (fun k => inner ℝ
            (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
              (halfExtent n) N
              (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
                halfExtent N hN beta hbeta n
                (Q.positiveHalfL2LinearMap hInvariant n
                  (R.realizableCarrierTranslation hInvariant n 1 (F k))))) z)
          atTop (𝓝 (physicalTopRawKernelCoefficient n f z))

/-- Projected synthesis density plus uniqueness of scalar limits turns the
finite realizable one-step raw-kernel limit into the completed raw-kernel weak
identity. Completion contributes no additional model assumption. -/
theorem completedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor_of_realizableOneStepLimit
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N)
    (hRaw : R.RealizableOneStepPhysicalTopRawKernelLimitAtFor hInvariant n f) :
    Q.CompletedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor
      hInvariant C n f := by
  intro z
  let x := physicalTopPairInput n f
  rcases R.exists_actualSynthesis_realizableOneStep_pair_inner_tendsto_completedBoundaryTransfer_two_pair
      hInvariant C n hCoherent x z with ⟨F, hstate, hCompleted⟩
  have hRawLimit : Tendsto
      (fun k => inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
            halfExtent N hN beta hbeta n
            (Q.positiveHalfL2LinearMap hInvariant n
              (R.realizableCarrierTranslation hInvariant n 1 (F k))))) z)
      atTop (𝓝 (physicalTopRawKernelCoefficient n f z)) := by
    apply hRaw z F
    simpa [x, physicalTopPairInput] using hstate
  have hEq := tendsto_nhds_unique hCompleted hRawLimit
  simpa [x, physicalTopPairInput, physicalTopRawKernelCoefficient] using hEq

/-- The finite-limit theorem generates the selected endpoint-pair weak
intertwining; the old completed `hWeak` is no longer an independent input. -/
theorem completedBoundaryTransferOneSlabPairWeakAtFor_physicalTop_of_realizableOneStepLimit
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N)
    (hRaw : R.RealizableOneStepPhysicalTopRawKernelLimitAtFor hInvariant n f) :
    Q.CompletedBoundaryTransferOneSlabPairWeakAtFor hInvariant C n f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        (halfExtent n) N hN (beta n) (hbeta n)) := by
  apply (Q.completedBoundaryTransferOneSlabPairWeakAtFor_physicalTop_iff_rawKernel
    hInvariant C n f).2
  exact R.completedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor_of_realizableOneStepLimit
    hInvariant C n hCoherent f hRaw

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

private theorem su2RealizableRawKernelLimitRankPositive : 0 < (2 : ℕ) := by
  norm_num

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

section SU2RealizableOneStepRawKernelLimit

variable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2RealizableRawKernelLimitRankPositive beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent 2 su2RealizableRawKernelLimitRankPositive beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 su2RealizableRawKernelLimitRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent 2 su2RealizableRawKernelLimitRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant C}

/-- SU(2) selected-mode weak coefficients are theorem-generated from explicit
common/realizable one-step coherence and the finite raw-kernel limit seam. -/
theorem su2CompletedBoundaryTransferPhysicalModeWeakAt_of_realizableOneStepRawKernelLimit
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2)
    (hCoherent : R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (hRaw : R.RealizableOneStepPhysicalTopRawKernelLimitAtFor hInvariant n f) :
    SU2CompletedBoundaryTransferPhysicalModeWeakAt
      (Q := Q) (hInvariant := hInvariant) (C := C) n f := by
  simpa [SU2CompletedBoundaryTransferPhysicalModeWeakAt] using
    R.completedBoundaryTransferOneSlabPairWeakAtFor_physicalTop_of_realizableOneStepLimit
      hInvariant C n hCoherent f hRaw

/-- Exact-gap continuum time-one eigenmode with the old completed weak family
replaced by explicit common/realizable one-step coherence and the finite
raw-kernel limit property. -/
theorem physicalOperator_one_apply_exactGapClusterContractionRatio_of_realizableOneStepRawKernelLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2RealizableRawKernelLimitRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2RealizableRawKernelLimitRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n psi) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hCoherent : ∀ n, R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (hRaw : ∀ n, R.RealizableOneStepPhysicalTopRawKernelLimitAtFor
      hInvariant n (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = exactGapClusterContractionRatio • psi := by
  apply physicalOperator_one_apply_exactGapClusterContractionRatio_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    A psi f mu hmu hf hBoundary
  intro n
  exact su2CompletedBoundaryTransferPhysicalModeWeakAt_of_realizableOneStepRawKernelLimit
    n (f n) (hCoherent n) (hRaw n)

/-- Public graph-closed vacuum-orthogonal Hamiltonian exact-gap mode with no
completed-boundary weak hypothesis. The selected model seam now lives entirely
at the realizable finite one-step/raw-kernel limit level. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_realizableOneStepRawKernelLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2RealizableRawKernelLimitRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric : T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2) (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (𝓝 exactGapClusterContractionRatio))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2RealizableRawKernelLimitRankPositive
        (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
      (A.approximate n (psi : P.PhysicalHilbert)) = su2CompletedBoundaryOneSlabModeBoundary
        (halfExtent n) (beta n) (hbeta n) (f n))
    (hCoherent : ∀ n, R.CommonSemigroupOneStepCoherentAt hInvariant C n)
    (hRaw : ∀ n, R.RealizableOneStepPhysicalTopRawKernelLimitAtFor
      hInvariant n (f n)) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧
        T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z =
          exactGapValueReal • psi := by
  apply exists_vacuumOrthogonalClosedRightHamiltonian_exactGapValueReal_mode_of_normalizedPhysicalTransferModeWeakMatrixCoefficients
    A hInnerSymmetric hHamiltonianSymmetric psi f mu hmu hf hBoundary
  intro n
  exact su2CompletedBoundaryTransferPhysicalModeWeakAt_of_realizableOneStepRawKernelLimit
    n (f n) (hCoherent n) (hRaw n)

end SU2RealizableOneStepRawKernelLimit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
