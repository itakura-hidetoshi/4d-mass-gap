import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2LiteralOneSidedDynamics
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance topEigenspaceBlockDynamicsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance topEigenspaceBlockDynamicsCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance topEigenspaceBlockDynamicsSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance topEigenspaceBlockDynamicsMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance topEigenspaceBlockDynamicsBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance topEigenspaceBlockDynamicsSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance topEigenspaceBlockDynamicsSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The full normalized-transfer top eigenspace, embedded isometrically into the
ambient one-slice Haar `L²` carrier.  No one-dimensionality of this eigenspace
is assumed. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta →ₗᵢ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) where
  toLinearMap :=
    { toFun := fun u =>
        ((u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      map_add' := by
        intro u v
        rfl
      map_smul' := by
        intro c u
        rfl }
  norm_map' := by
    intro u
    rfl

private theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u := by
  let Tphys := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let lambda : ℝ := ‖Tphys‖
  have hlambdaPos : 0 < lambda := by
    simpa [lambda, Tphys] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hlambdaNe : lambda ≠ 0 := hlambdaPos.ne'
  have hfix :
      S (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
        H N hN beta hbeta
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)).1
        u.property
  have hraw :
      Tphys (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda •
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    have h := congrArg
      (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
        lambda • z) hfix
    change
      lambda • (lambda⁻¹ •
        Tphys (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) =
      lambda •
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) at h
    simpa [smul_smul, hlambdaNe] using h
  change
    ((Tphys (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
    lambda •
      (((u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  exact congrArg
    (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      (z : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    hraw

private theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspaceOrthogonal
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
  have hraw :
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
    hraw

/-- The literal raw pair transfer acts by the raw top eigenvalue squared on the
full top-top decomposable block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_top_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta v)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta v) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspace,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspace,
    realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
  ring_nf

/-- Mixed block with an excitation on the left and an arbitrary top mode on the
right. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_orthogonal_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta f))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspaceOrthogonal,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspace,
    realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
  ring_nf

/-- Mixed block with an arbitrary top mode on the left and an excitation on the
right. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_top_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta f)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspace,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspaceOrthogonal,
    realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
  ring_nf

/-- Double-excitation block: both normalized factors evolve by the strict
orthogonal restriction, while the raw pair normalization remains exactly
`‖T_phys‖²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_orthogonal_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspaceOrthogonal,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_topEigenspaceOrthogonal,
    realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
  ring_nf

/-- Exact natural powers on the left-excitation/right-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ k) f))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  change (T ^ k) _ = c ^ k • _
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      change (T ^ k) (T _) = _
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_orthogonal_top]
      rw [map_smul, ih]
      simp only [pow_succ, smul_smul]
      ring

/-- Exact natural powers on the left-top/right-excitation block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_top_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ k) f)) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  change (T ^ k) _ = c ^ k • _
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      change (T ^ k) (T _) = _
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_top_orthogonal]
      rw [map_smul, ih]
      simp only [pow_succ, smul_smul]
      ring

/-- Exact natural powers on the double-excitation block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  change (T ^ k) _ = c ^ k • _
  induction k generalizing f g with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      change (T ^ k) (T _) = _
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_orthogonal_orthogonal]
      rw [map_smul, ih]
      simp only [pow_succ, smul_smul]
      ring

/-- Positive-time norm decay on the left-excitation/right-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_top_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) (hk : 0 < k)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u))‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ k * ‖f‖ * ‖u‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_top]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _),
    realL2ExternalTensor_norm,
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta).norm_map,
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta).norm_map]
  have hR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
      H N hN beta hbeta k hk f
  nlinarith [norm_nonneg u,
    pow_nonneg (sq_nonneg
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖) k]

/-- Positive-time norm decay on the left-top/right-excitation block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_top_orthogonal_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) (hk : 0 < k)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f))‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ k * ‖u‖ * ‖f‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_top_orthogonal]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _),
    realL2ExternalTensor_norm,
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta).norm_map,
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta).norm_map]
  have hR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
      H N hN beta hbeta k hk f
  nlinarith [norm_nonneg u,
    pow_nonneg (sq_nonneg
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖) k]

/-- Positive-time doubled decay on the double-excitation block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_orthogonal_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) (hk : 0 < k)
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
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ k) ^ 2 * ‖f‖ * ‖g‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_orthogonal]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _),
    realL2ExternalTensor_norm,
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta).norm_map,
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta).norm_map]
  have hf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
      H N hN beta hbeta k hk f
  have hg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
      H N hN beta hbeta k hk g
  have hc : 0 ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k :=
    pow_nonneg (sq_nonneg _) _
  have hq : 0 ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ k :=
    pow_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pos
        H N hN beta hbeta).le _
  nlinarith [norm_nonneg f, norm_nonneg g]

/-- Audit-visible fixed-finite-volume block hierarchy.  The full top eigenspace
is retained, so no vacuum-uniqueness assumption is hidden.  Mixed blocks decay
at one factor `q^k`, the double-excitation block at `q^(2k)`, while the top-top
block is the noncontracting raw-normalization block. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_topEigenspaceBlockFiniteVolumeDecay
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ q : ℝ,
      0 < q ∧ q < 1 ∧
      (∀ (k : ℕ), 0 < k →
        ∀ (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta)
          (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta),
          ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta ^ k)
              (realL2ExternalTensor
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
                  H N hN beta hbeta f)
                (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
                  H N hN beta hbeta u))‖ ≤
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖ ^ 2) ^ k * q ^ k * ‖f‖ * ‖u‖) ∧
      (∀ (k : ℕ), 0 < k →
        ∀ (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta)
          (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta),
          ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta ^ k)
              (realL2ExternalTensor
                (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
                  H N hN beta hbeta u)
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
                  H N hN beta hbeta f))‖ ≤
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖ ^ 2) ^ k * q ^ k * ‖u‖ * ‖f‖) ∧
      (∀ (k : ℕ), 0 < k →
        ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta,
          ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta ^ k)
              (realL2ExternalTensor
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
                  H N hN beta hbeta f)
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
                  H N hN beta hbeta g))‖ ≤
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖ ^ 2) ^ k * (q ^ k) ^ 2 * ‖f‖ * ‖g‖) := by
  let q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
    H N hN beta hbeta
  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pos
        H N hN beta hbeta
  · simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_lt_one
        H N hN beta hbeta
  · intro k hk f u
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_top_norm_le
        H N hN beta hbeta k hk f u
  · intro k hk u f
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_top_orthogonal_norm_le
        H N hN beta hbeta k hk u f
  · intro k hk f g
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_orthogonal_orthogonal_norm_le
        H N hN beta hbeta k hk f g

end

end MathlibAnalytic
end MGAP4D
