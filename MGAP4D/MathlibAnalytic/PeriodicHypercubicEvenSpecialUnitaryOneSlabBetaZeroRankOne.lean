import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import Mathlib.Tactic

/-!
# Exact beta-zero rank-one form of the one-slab Haar-L2 transfer

At zero Wilson coupling the literal temporal-gauge one-slab kernel is exactly
the constant function one.  Consequently its product-Haar L2 kernel vector is
the external tensor of the normalized constant-one Haar vector with itself,
and the ambient one-slab transfer is the corresponding rank-one orthogonal
projection.

This is an exact finite-volume endpoint statement.  It does not yet identify
the physical Gauss-law restriction, the chosen ground-state vector, or the
ground-state joint measure.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroOneSlabRankOneSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroOneSlabRankOneSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At zero coupling the exact one-slab Wilson kernel is identically one. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_zero
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N 0 A B = 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  norm_num

/-- Canonical constant-one vector in the spatial-slice Haar L2 carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2
    (H N : ℕ) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  Lp.const 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (1 : ℝ)

/-- The constant-one Haar L2 vector has unit norm. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2_norm
    (H N : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N‖ = 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change ‖Lp.const 2 μ (1 : ℝ)‖ = 1
  simpa [measureReal_def] using
    (Lp.norm_const (μ := μ) (p := 2) (c := (1 : ℝ)) (by norm_num))

/-- The beta-zero one-slab kernel L2 vector is exactly the external tensor of
the normalized Haar constant-one vector with itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_zero_eq_externalTensor
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN 0 (by norm_num) =
      realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneL2 : Lp ℝ 2 μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N
  have hOne :
      (fun A => oneL2 A) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    simpa [oneL2,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2] using
      (Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ)))
  have hOneFst :
      (fun z : _ × _ => oneL2 z.1) =ᵐ[μ.prod μ]
        (fun _ => (1 : ℝ)) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hOne
  have hOneSnd :
      (fun z : _ × _ => oneL2 z.2) =ᵐ[μ.prod μ]
        (fun _ => (1 : ℝ)) :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hOne
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN 0 (by norm_num) =
      realL2ExternalTensor oneL2 oneL2
  apply Lp.ext
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H N hN 0 (by norm_num),
    realL2ExternalTensor_coeFn oneL2 oneL2,
    hOneFst,
    hOneSnd] with z hK hTensor hfst hsnd
  rw [hK]
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N 0 z.1 z.2 = 1 := by
      exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_zero
        H N z.1 z.2
    _ = realL2ExternalTensorFunction oneL2 oneL2 z := by
      simp [realL2ExternalTensorFunction, hfst, hsnd]
    _ = realL2ExternalTensor oneL2 oneL2 z := hTensor.symm

/-- A square separable Hilbert-Schmidt kernel is the corresponding rank-one
operator. -/
theorem realL2HilbertSchmidtKernelOperator_externalTensor_apply
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    [SFinite μ]
    (u v f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelOperator
        (realL2ExternalTensor u v) f =
      (inner ℝ u f) • v := by
  apply ext_inner_right ℝ
  intro g
  rw [realL2HilbertSchmidtKernelOperator_inner,
    realL2HilbertSchmidtKernelPairing_externalTensor,
    real_inner_smul_left]

/-- Exact beta-zero action of the ambient one-slab transfer: Haar mean
projection onto the constant-one line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_apply
    (H N : ℕ)
    (hN : 0 < N)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN 0 (by norm_num) f =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N) f) •
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_zero_eq_externalTensor
      H N hN]
  exact
    realL2HilbertSchmidtKernelOperator_externalTensor_apply
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N)
      f

/-- Operator form of the same endpoint identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_eq_rankOne
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN 0 (by norm_num) =
      InnerProductSpace.rankOne ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_apply
      H N hN f,
    InnerProductSpace.rankOne_apply]

/-- The ambient beta-zero transfer fixes the normalized constant-one mode. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_one
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N := by
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_apply]
  rw [real_inner_self_eq_norm_sq,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2_norm]
  norm_num

end

end MGAP4D.MathlibAnalytic
