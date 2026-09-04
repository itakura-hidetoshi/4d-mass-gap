import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2LiteralOneSidedDynamics
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance twoSidedDoubleDynamicsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoSidedDoubleDynamicsCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoSidedDoubleDynamicsSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoSidedDoubleDynamicsMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoSidedDoubleDynamicsBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoSidedDoubleDynamicsSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoSidedDoubleDynamicsSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The raw one-slab transfer acts on a physical excitation by the exact raw
vacuum eigenvalue times the normalized top-eigenspace orthogonal restriction.
This isolates the one-factor identity used by both endpoint sectors below. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_physicalExcitation_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta f) := by
  let Tphys := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    H N hN beta hbeta
  let lambda : ℝ := ‖Tphys‖
  have hlambdaPos : 0 < lambda := by
    simpa [lambda, Tphys] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hlambdaNe : lambda ≠ 0 := hlambdaPos.ne'
  have hTphysEq :
      Tphys (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda • S (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    change
      Tphys (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda • (lambda⁻¹ •
          Tphys (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
    rw [smul_smul, mul_inv_cancel₀ hlambdaNe, one_smul]
  have hRcoe :
      ((R f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      S (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    rfl
  have hTphysR :
      Tphys (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda •
          ((R f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    rw [hTphysEq, hRcoe]
  change
    ((Tphys (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
    lambda •
      (((R f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact congrArg
    (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      (z : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    hTphysR

/-- The raw one-slab transfer sends the normalized physical top mode to the
same mode multiplied by the raw physical transfer norm. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_topMode_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta := by
  let Tphys := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  change
    ((Tphys
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
    ‖Tphys‖ •
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact congrArg
    (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      (z : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
      H N hN beta hbeta)

/-- Every natural power of the literal pair transfer factorizes on a pure
external tensor into the corresponding powers of the two raw one-slab
transfers. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_apply_externalTensor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k) (realL2ExternalTensor f g) =
      realL2ExternalTensor
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta ^ k) f)
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta ^ k) g) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let Tp := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    H N hN beta hbeta
  change (Tp ^ k) (realL2ExternalTensor f g) =
    realL2ExternalTensor ((T ^ k) f) ((T ^ k) g)
  induction k generalizing f g with
  | zero => simp
  | succ k ih =>
      change (Tp ^ k) (Tp (realL2ExternalTensor f g)) =
        realL2ExternalTensor ((T ^ k) (T f)) ((T ^ k) (T g))
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
      exact ih (T f) (T g)

/-- Right-endpoint physical excitation embedding `Ω_top ⊠ f`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N where
  toFun f :=
    realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta f)
  map_add' f g := by
    rw [map_add, realL2ExternalTensor_add_right]
    rfl
  map_smul' c f := by
    rw [map_smul, realL2ExternalTensor_smul_right]
    rfl

/-- The right-endpoint embedding is an exact linear isometry. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N where
  toLinearMap :=
    periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearMap
      H N hN beta hbeta
  norm_map' f := by
    change
      ‖realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)‖ = ‖f‖
    rw [realL2ExternalTensor_norm,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2_norm]
    rw [(periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta).norm_map]
    simp

/-- Literal pair transfer preserves the represented right one-sided sector and
acts there by the same compressed excitation operator as on the left sector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_rightSidedExcitation_apply_eq_compressed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta f) := by
  let lambda : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    H N hN beta hbeta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let C := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    H N hN beta hbeta
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta (realL2ExternalTensor Omega (E f)) =
      realL2ExternalTensor Omega (E (C f))
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_topMode_apply,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_physicalExcitation_apply]
  calc
    realL2ExternalTensor (lambda • Omega) (lambda • E (R f)) =
        lambda ^ 2 • realL2ExternalTensor Omega (E (R f)) := by
      rw [realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
      ring_nf
    _ = realL2ExternalTensor Omega (E (C f)) := by
      rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_apply]
      change
        lambda ^ 2 • realL2ExternalTensor Omega (E (R f)) =
          realL2ExternalTensor Omega (E (lambda ^ 2 • R f))
      rw [map_smul, realL2ExternalTensor_smul_right]

/-- Exact right-sector intertwining for every natural power. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_rightSidedExcitation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k) f) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    H N hN beta hbeta
  let C := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    H N hN beta hbeta
  let J := periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
    H N hN beta hbeta
  change (T ^ k) (J f) = J ((C ^ k) f)
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      change (T ^ k) (T (J f)) = J ((C ^ k) (C f))
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_rightSidedExcitation_apply_eq_compressed]
      exact ih (C f)

/-- The right one-sided literal dynamics has the same finite-volume relative
exponential decay as the left one-sided sector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_rightSidedExcitation_finiteVolumeRelativeExponentialDecay
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∃ q : ℝ,
      0 ≤ q ∧ q < 1 ∧
      ∀ (k : ℕ)
        (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta),
        ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta ^ k)
            (periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
              H N hN beta hbeta f)‖ ≤
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ ^ 2) ^ k * q ^ k * ‖f‖ := by
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  refine ⟨q, ?_, ?_, ?_⟩
  · dsimp [q]
    exact norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
  · simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  · intro k f
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_rightSidedExcitation]
    rw [(periodicHypercubicEvenSpecialUnitaryRightSidedExcitationPairLinearIsometry
      H N hN beta hbeta).norm_map]
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_apply_norm_le
        H N hN beta hbeta k f

/-- Exact one-step dynamics for a decomposable pair of physical excitations.
Both normalized excitation factors contract, while the raw pair-vacuum
normalization remains exactly `‖T_phys‖²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_doubleExcitation_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta f))
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta g)) := by
  let lambda : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_physicalExcitation_apply,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_physicalExcitation_apply]
  change realL2ExternalTensor (lambda • E (R f)) (lambda • E (R g)) =
    lambda ^ 2 • realL2ExternalTensor (E (R f)) (E (R g))
  rw [realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
  ring_nf

/-- A generic pointwise power bound avoiding operator-space scalar-tower
reconstruction on the concrete physical orthogonal subtype. -/
private theorem continuousLinearMap_pow_apply_norm_le_norm_pow
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (k : ℕ)
    (f : E) :
    ‖(R ^ k) f‖ ≤ ‖R‖ ^ k * ‖f‖ := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      change ‖(R ^ k) (R f)‖ ≤ ‖R‖ ^ (k + 1) * ‖f‖
      calc
        ‖(R ^ k) (R f)‖ ≤ ‖R‖ ^ k * ‖R f‖ := ih (R f)
        _ ≤ ‖R‖ ^ k * (‖R‖ * ‖f‖) :=
          mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm R f)
            (pow_nonneg (norm_nonneg R) k)
        _ = ‖R‖ ^ (k + 1) * ‖f‖ := by
          rw [pow_succ]
          ring

/-- Exact double-excitation dynamics for every natural power. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_doubleExcitation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g)) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ k) f))
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ k) g)) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  change
    (T ^ k) (realL2ExternalTensor (E f) (E g)) =
      c ^ k • realL2ExternalTensor (E ((R ^ k) f)) (E ((R ^ k) g))
  induction k generalizing f g with
  | zero => simp
  | succ k ih =>
      change
        (T ^ k) (T (realL2ExternalTensor (E f) (E g))) =
          c ^ (k + 1) •
            realL2ExternalTensor (E ((R ^ k) (R f))) (E ((R ^ k) (R g)))
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_doubleExcitation_apply]
      change
        (T ^ k) (c • realL2ExternalTensor (E (R f)) (E (R g))) = _
      calc
        (T ^ k) (c • realL2ExternalTensor (E (R f)) (E (R g))) =
            c • (T ^ k) (realL2ExternalTensor (E (R f)) (E (R g))) := by
          exact (T ^ k).map_smul c _
        _ = c • (c ^ k •
              realL2ExternalTensor (E ((R ^ k) (R f))) (E ((R ^ k) (R g)))) := by
          rw [ih (R f) (R g)]
        _ = c ^ (k + 1) •
              realL2ExternalTensor (E ((R ^ k) (R f))) (E ((R ^ k) (R g))) := by
          rw [smul_smul, pow_succ]
          ring_nf

/-- The double-excitation norm decays with the square of the normalized
one-factor contraction. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_doubleExcitation_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g))‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k * ‖f‖ * ‖g‖ := by
  let E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_doubleExcitation]
  change
    ‖c ^ k • realL2ExternalTensor (E ((R ^ k) f)) (E ((R ^ k) g))‖ ≤
      c ^ k * (‖R‖ ^ 2) ^ k * ‖f‖ * ‖g‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) k)]
  rw [realL2ExternalTensor_norm, E.norm_map, E.norm_map]
  have hf := continuousLinearMap_pow_apply_norm_le_norm_pow R k f
  have hg := continuousLinearMap_pow_apply_norm_le_norm_pow R k g
  have hc : 0 ≤ c ^ k := pow_nonneg (sq_nonneg _) k
  have hRk : 0 ≤ ‖R‖ ^ k := pow_nonneg (norm_nonneg R) k
  calc
    c ^ k * (‖(R ^ k) f‖ * ‖(R ^ k) g‖) ≤
        c ^ k * ((‖R‖ ^ k * ‖f‖) * (‖R‖ ^ k * ‖g‖)) := by
      gcongr
    _ = c ^ k * (‖R‖ ^ 2) ^ k * ‖f‖ * ‖g‖ := by
      rw [← mul_pow]
      ring

/-- Audit-visible fixed-finite-volume double-excitation decay package.  The
witness is the squared normalized excitation contraction, so both excited
endpoints contribute.  This is not a full pair-vacuum-complement theorem and
is not scale-uniform or continuum. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_doubleExcitation_finiteVolumeRelativeExponentialDecay
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∃ q : ℝ,
      0 ≤ q ∧ q < 1 ∧
      ∀ (k : ℕ)
        (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta),
        ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta ^ k)
            (realL2ExternalTensor
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
                H N hN beta hbeta f)
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
                H N hN beta hbeta g))‖ ≤
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ ^ 2) ^ k * q ^ k * ‖f‖ * ‖g‖ := by
  let r :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  let q := r ^ 2
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
  have hr1 : r < 1 := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact sq_nonneg r
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  refine ⟨q, hq0, hq1, ?_⟩
  intro k f g
  simpa [q, r] using
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_doubleExcitation_norm_le
      H N hN beta hbeta k f g

end

end MathlibAnalytic
end MGAP4D
