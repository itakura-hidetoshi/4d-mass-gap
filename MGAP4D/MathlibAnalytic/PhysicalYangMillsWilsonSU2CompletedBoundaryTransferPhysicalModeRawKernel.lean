import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferPhysicalModeMatrixCoefficient
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelBilinear
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance physicalModeRawKernelSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalModeRawKernelTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalModeRawKernelCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalModeRawKernelSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalModeRawKernelMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalModeRawKernelBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalModeRawKernelSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalModeRawKernelSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Forgetting the Gauss-law subtype after one normalized physical transfer is
exactly the normalized raw one-slab Haar-L2 transfer.

This is the operator normalization identity needed before rewriting arbitrary
pair-Haar matrix coefficients in literal Wilson-kernel form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_normalizedRaw
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        H N hN beta hbeta f =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ •
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
  simp only [Submodule.coe_smul]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe]

/-- The generic physical-mode one-step wrapper fixes the chosen top mode.

The existing top-mode theorem is stated through the dedicated top wrapper;
this form is convenient for the pointwise pair predicate, whose companion is
supplied as an ordinary gauge-invariant mode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_top_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
        H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
  simpa using congrArg
    (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      (z : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta)

/-- Arbitrary pair-Haar matrix coefficients of the selected one-particle
one-step tensor admit an exact raw-Wilson normal form.

No density restriction on the test vector `z` is used.  Real-inner symmetry
turns `z` itself into a Hilbert-Schmidt kernel; the primary endpoint contributes
one normalized raw one-slab transfer, while the chosen companion top mode is
fixed.  Thus the right side is ready for literal Wilson/Fubini expansion. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStep_top_inner_eq_rawKernel
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
              H N hN beta hbeta))) z =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        realL2HilbertSchmidtKernelPairing z
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_top_eq]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_normalizedRaw]
  unfold periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
  rw [real_inner_comm]
  change
    realL2HilbertSchmidtKernelPairing z
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ •
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f))
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
          H N hN beta hbeta) = _
  rw [realL2HilbertSchmidtKernelPairing_smul_left]
  rfl

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

/-- Raw-Wilson normal form of the selected-mode completed-boundary seam.

For every ambient pair-Haar test kernel `z`, the completed OS boundary transfer
matrix coefficient must equal one explicit normalized one-slab Wilson kernel
pairing.  This predicate is not weaker than the preceding selected-mode weak
predicate: the theorem below proves exact equivalence.

The remaining finite/common-time coherence is still visible through
`Q.completedBoundaryTransfer hInvariant C n 2`; no identification of the
abstract common translation with lattice translation is inserted here. -/
def CompletedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
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
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) N hN (beta n) (hbeta n)))) z =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖⁻¹ *
        realL2HilbertSchmidtKernelPairing z
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N f))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) N hN (beta n) (hbeta n))

/-- The selected-pair weak intertwining from the previous unit is exactly the
raw one-slab Wilson kernel identity above.

This is an equality of proof obligations, not an implication obtained by
adding a new hypothesis.  In particular, arbitrary pair-Haar tests are retained
and no decomposable-tensor density theorem is required. -/
theorem completedBoundaryTransferOneSlabPairWeakAtFor_physicalTop_iff_rawKernel
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N) :
    CompletedBoundaryTransferOneSlabPairWeakAtFor
        Q hInvariant C n f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          (halfExtent n) N hN (beta n) (hbeta n)) ↔
      CompletedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor
        Q hInvariant C n f := by
  constructor
  · intro hWeak z
    have hz := hWeak z
    change inner ℝ
        (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2)
          (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) N hN (beta n) (hbeta n)))) z = _
    simpa [CompletedBoundaryTransferOneSlabPairWeakAtFor] using
      hz.trans
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStep_top_inner_eq_rawKernel
          (halfExtent n) N hN (beta n) (hbeta n) f z)
  · intro hRaw z
    have hz := hRaw z
    change inner ℝ
        (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2)
          (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
              (halfExtent n) N
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
                (halfExtent n) N hN (beta n) (hbeta n))))) z = _
    have hTop :
        periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
              (halfExtent n) N hN (beta n) (hbeta n)) =
          periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) N hN (beta n) (hbeta n) := by
      rfl
    rw [hTop]
    calc
      inner ℝ
          (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
            (halfExtent n) N
            (Q.completedBoundaryTransfer hInvariant C n 2)
            (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
              (halfExtent n) N
              (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
                (halfExtent n) N f)
              (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
                (halfExtent n) N hN (beta n) (hbeta n)))) z =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)‖⁻¹ *
          realL2HilbertSchmidtKernelPairing z
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)
              (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
                (halfExtent n) N f))
            (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
              (halfExtent n) N hN (beta n) (hbeta n)) := hz
      _ = inner ℝ
          (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
            (halfExtent n) N
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
              (halfExtent n) N hN (beta n) (hbeta n) f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
              (halfExtent n) N hN (beta n) (hbeta n)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
                (halfExtent n) N hN (beta n) (hbeta n)))) z :=
        (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStep_top_inner_eq_rawKernel
          (halfExtent n) N hN (beta n) (hbeta n) f z).symm

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
