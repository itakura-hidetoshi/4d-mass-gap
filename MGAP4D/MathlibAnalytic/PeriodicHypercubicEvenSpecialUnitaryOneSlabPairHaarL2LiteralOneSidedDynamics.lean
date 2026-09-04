import MGAP4D.MathlibAnalytic.RealL2BoundedKernelIntegralRepresentation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalCompressedTransferPowers
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance literalOneSidedDynamicsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance literalOneSidedDynamicsCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance literalOneSidedDynamicsSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance literalOneSidedDynamicsMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance literalOneSidedDynamicsBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance literalOneSidedDynamicsSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance literalOneSidedDynamicsSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance literalOneSidedDynamicsSpatialSlicePairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The literal ordered-pair Wilson transfer acts on every decomposable
pair-Haar `L²` vector as the external tensor product of the two raw one-slab
transfers.

This is an equality of vectors, not only of decomposable matrix coefficients.
It follows from the literal Fubini representative of the bounded
Hilbert--Schmidt kernel operators. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta (realL2ExternalTensor f g) =
      realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta g) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let k := fun A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B
  let kp := fun
      p q : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    k p.1 q.1 * k p.2 q.2
  have hkMeas :
      AEStronglyMeasurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          k z.1 z.2)
        (μ.prod μ) := by
    simpa [μ, k] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).measurable.aestronglyMeasurable
  have hkBound : ∀ A B, |k A B| ≤ 1 := by
    intro A B
    simpa [k] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
  have hkpMeas :
      AEStronglyMeasurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
          kp z.1 z.2)
        ((μ.prod μ).prod (μ.prod μ)) := by
    simpa [μ, kp, k,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_aestronglyMeasurable
        H N beta
  have hkpBound : ∀ p q, |kp p q| ≤ 1 := by
    intro p q
    simpa [kp, k,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
        H N hN beta hbeta (p, q)
  have hK :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta =ᵐ[μ.prod μ]
        fun z => k z.1 z.2 := by
    simpa [μ, k,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN beta hbeta
  have hKp :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta =ᵐ[(μ.prod μ).prod (μ.prod μ)]
        fun z => kp z.1 z.2 := by
    simpa [μ, kp, k,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta
  let Of := realL2BoundedKernelIntegralOutputL2
    (μ := μ) k hkMeas hkBound f
  let Og := realL2BoundedKernelIntegralOutputL2
    (μ := μ) k hkMeas hkBound g
  let Op := realL2BoundedKernelIntegralOutputL2
    (μ := μ.prod μ) kp hkpMeas hkpBound (realL2ExternalTensor f g)
  have hfApply :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f = Of := by
    change
      realL2HilbertSchmidtKernelOperator
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
            H N hN beta hbeta) f = Of
    simpa [Of] using
      (realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
        (μ := μ) k
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta)
        hK hkMeas hkBound f)
  have hgApply :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta g = Og := by
    change
      realL2HilbertSchmidtKernelOperator
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
            H N hN beta hbeta) g = Og
    simpa [Og] using
      (realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
        (μ := μ) k
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta)
        hK hkMeas hkBound g)
  have hpApply :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor f g) = Op := by
    change
      realL2HilbertSchmidtKernelOperator
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
            H N hN beta hbeta)
          (realL2ExternalTensor f g) = Op
    simpa [Op] using
      (realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
        (μ := μ.prod μ) kp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta)
        hKp hkpMeas hkpBound (realL2ExternalTensor f g))
  rw [hpApply, hfApply, hgApply]
  have hInput := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f g
  have hFiber : ∀ y,
      realL2BoundedKernelIntegralOutput
          (μ := μ.prod μ) kp (realL2ExternalTensor f g) y =
        realL2BoundedKernelIntegralOutput (μ := μ) k f y.1 *
          realL2BoundedKernelIntegralOutput (μ := μ) k g y.2 := by
    intro y
    unfold realL2BoundedKernelIntegralOutput
    calc
      (∫ x :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          kp x y * realL2ExternalTensor f g x ∂(μ.prod μ)) =
        ∫ x :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          (k x.1 y.1 * f x.1) * (k x.2 y.2 * g x.2) ∂(μ.prod μ) := by
            apply integral_congr_ae
            filter_upwards [hInput] with x hx
            rw [hx]
            simp only [realL2ExternalTensorFunction]
            dsimp [kp]
            ring
      _ = (∫ x, k x y.1 * f x ∂μ) * (∫ x, k x y.2 * g x ∂μ) := by
        exact integral_prod_mul
          (fun x => k x y.1 * f x)
          (fun x => k x y.2 * g x)
      _ = _ := rfl
  apply Lp.ext
  have hOp :=
    realL2BoundedKernelIntegralOutputL2_coeFn
      (μ := μ.prod μ) kp hkpMeas hkpBound (realL2ExternalTensor f g)
  have hTensor := realL2ExternalTensor_coeFn
    (μ := μ) (ν := μ) Of Og
  have hOf := realL2BoundedKernelIntegralOutputL2_coeFn
    (μ := μ) k hkMeas hkBound f
  have hOg := realL2BoundedKernelIntegralOutputL2_coeFn
    (μ := μ) k hkMeas hkBound g
  have hOfPair :
      (fun y :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => Of y.1) =ᵐ[μ.prod μ]
        fun y => realL2BoundedKernelIntegralOutput (μ := μ) k f y.1 := by
    simpa [Of, Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hOf
  have hOgPair :
      (fun y :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => Og y.2) =ᵐ[μ.prod μ]
        fun y => realL2BoundedKernelIntegralOutput (μ := μ) k g y.2 := by
    simpa [Og, Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hOg
  filter_upwards [hOp, hTensor, hOfPair, hOgPair] with y hop ht hof hog
  rw [hop, ht]
  simp only [realL2ExternalTensorFunction]
  rw [hof, hog, hFiber y]

/-- On the represented physical one-sided excitation sector, the literal raw
pair transfer is not merely represented by the compressed operator in matrix
coefficients: it actually preserves the range and satisfies the exact vector
intertwining

`T_pair (J f) = J (C f)`.

The raw pair-vacuum normalization `‖T_phys‖²` remains explicit through `C`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_apply_eq_compressed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta f) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  let Tphys := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  let C := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    H N hN beta hbeta
  let J := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
    H N hN beta hbeta
  let E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    H N hN beta hbeta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
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
  have hFirst : T (E f) = lambda • E (R f) := by
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
  have hOmegaPhys :
      Tphys
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta) =
        lambda •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta := by
    simpa [lambda, Tphys] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
        H N hN beta hbeta)
  have hOmega : T Omega = lambda • Omega := by
    change
      ((Tphys
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      lambda •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    exact congrArg
      (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
        (z : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
      hOmegaPhys
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta (realL2ExternalTensor (E f) Omega) =
      realL2ExternalTensor (E (C f)) Omega
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor]
  calc
    realL2ExternalTensor (T (E f)) (T Omega) =
        realL2ExternalTensor (lambda • E (R f)) (lambda • Omega) := by
      rw [hFirst, hOmega]
    _ = lambda ^ 2 • realL2ExternalTensor (E (R f)) Omega := by
      rw [realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
      ring_nf
    _ = realL2ExternalTensor (E (C f)) Omega := by
      rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_apply]
      change
        lambda ^ 2 • realL2ExternalTensor (E (R f)) Omega =
          realL2ExternalTensor (E (lambda ^ 2 • R f)) Omega
      rw [map_smul, realL2ExternalTensor_smul_left]

/-- Explicit range-invariance witness for the literal pair transfer on the
one-sided physical excitation sector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_range_invariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ∃ g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta f) =
        periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta g := by
  refine ⟨periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    H N hN beta hbeta f, ?_⟩
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_apply_eq_compressed
      H N hN beta hbeta f

/-- Exact intertwining of every natural power of the literal raw pair transfer
with the corresponding power of the represented compressed excitation
operator. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_oneSidedExcitation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k) f) := by
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    H N hN beta hbeta
  let C := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    H N hN beta hbeta
  let J := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
    H N hN beta hbeta
  change (T ^ k) (J f) = J ((C ^ k) f)
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      change (T ^ k) (T (J f)) = J ((C ^ k) (C f))
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_apply_eq_compressed]
      exact ih (C f)

/-- Because the one-sided embedding is an isometry, the literal pair-transfer
power has exactly the same vector norm on this sector as the represented
compressed power. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_oneSidedExcitation_norm_eq_compressed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta f)‖ =
      ‖(periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k) f‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_oneSidedExcitation]
  exact
    (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
      H N hN beta hbeta).norm_map _

/-- Literal fixed-finite-volume one-sided pair dynamics obeys the exact raw
pair-vacuum normalization power times the normalized physical excitation
geometric factor. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_oneSidedExcitation_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta ^ k)
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta f)‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ k * ‖f‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_oneSidedExcitation_norm_eq_compressed]
  exact
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_apply_norm_le
      H N hN beta hbeta k f

/-- Audit-visible literal finite-volume relative exponential decay package.
The witness is the norm of the normalized physical top-eigenspace orthogonal
restriction.  This is neither a full pair-vacuum-complement contraction nor a
scale-uniform or continuum statement. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_finiteVolumeRelativeExponentialDecay
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
            (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
              H N hN beta hbeta f)‖ ≤
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖ ^ 2) ^ k * q ^ k * ‖f‖ := by
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      (norm_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta))
  · simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  · intro k f
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_oneSidedExcitation_norm_le
        H N hN beta hbeta k f

end

end MathlibAnalytic
end MGAP4D