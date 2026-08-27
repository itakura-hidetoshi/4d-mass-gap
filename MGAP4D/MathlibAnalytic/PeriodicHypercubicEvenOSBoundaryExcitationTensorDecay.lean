import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance osBoundaryExcitationTensorDecaySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationTensorDecaySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationTensorDecaySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationTensorDecaySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationTensorDecaySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationTensorDecaySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationTensorDecaySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Forget only the invariant-subspace wrappers and read one physical
excitation as an honest one-slice Haar-`L²` vector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta f‖ = ‖f‖ :=
  rfl

/-- A pair of physical excitations defines the canonical external-tensor vector
on the two reflection-fixed spatial endpoint slices. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2 H N hN beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2 H N hN beta hbeta g)

/-- Exact cross norm of the two-endpoint excitation tensor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
        H N hN beta hbeta f g‖ = ‖f‖ * ‖g‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2]
  rw [realL2ExternalTensor_norm]
  simp

/-- Evolve both endpoint excitations for the same positive integer Euclidean
time and form their external tensor on the pair carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
    H N hN beta hbeta
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f)
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) g)

/-- On the pure excitation-tensor core, evolving both endpoints produces the
product of the two one-slice norms. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
        H N hN beta hbeta n f g‖ =
      ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f‖ *
        ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g‖ := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2_norm]

/-- The concrete two-endpoint excitation tensor decays at twice the one-slice
finite-volume logarithmic rate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
        H N hN beta hbeta n f g‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * (‖f‖ * ‖g‖) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer_norm]
  have hf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
      H N hN beta hbeta n hn f
  have hg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
      H N hN beta hbeta n hn g
  have hnonnegf : 0 ≤
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖ :=
    mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hmul := mul_le_mul hf hg (norm_nonneg _) hnonnegf
  calc
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f‖ *
        ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g‖ ≤
      (Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖f‖) *
        (Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖g‖) := hmul
    _ = Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * (‖f‖ * ‖g‖) := by
      rw [← Real.exp_add]
      ring

/-- Pull the evolved two-endpoint excitation tensor back to the actual shared
reflection-fixed boundary `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N :=
  periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
      H N hN beta hbeta n f g)

/-- Boundary reindexing is isometric, so the same doubled exponential decay
holds on the actual shared Wilson boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer
        H N hN beta hbeta n f g‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * (‖f‖ * ‖g‖) := by
  unfold periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer
  rw [(periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).norm_map]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer_norm_le_exp
    H N hN beta hbeta n hn f g

/-- Audit-visible receipt for the concrete finite-volume excitation tensor core
on the actual shared Wilson boundary. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationTensorDecayPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  pairCrossNorm :
    ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
          H N hN beta hbeta f g‖ = ‖f‖ * ‖g‖
  boundaryTensorDecay :
    ∀ (n : ℕ), 0 < n →
      ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer
          H N hN beta hbeta n f g‖ ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * (‖f‖ * ‖g‖)

/-- Construct the concrete shared-boundary excitation tensor decay package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationTensorDecayPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationTensorDecayPackage
      H N hN beta hbeta :=
  { pairCrossNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2_norm
        H N hN beta hbeta
    boundaryTensorDecay :=
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer_norm_le_exp
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
