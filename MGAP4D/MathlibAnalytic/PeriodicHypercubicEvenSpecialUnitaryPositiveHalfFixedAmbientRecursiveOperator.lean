import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveMessageL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSymmetricKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance positiveHalfFixedAmbientRecursiveOperatorIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveOperatorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveOperatorSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveOperatorMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveOperatorBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveOperatorSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfFixedAmbientRecursiveOperatorPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

private theorem positiveHalfFixedAmbientRecursiveOperator_real_inner_eq_mul
    (a b : ℝ) : inner ℝ a b = a * b := by
  have hOneInner : inner ℝ (1 : ℝ) (1 : ℝ) = 1 := by
    have h := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (1 : ℝ)
    norm_num at h ⊢
  calc
    inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
    _ = b * inner ℝ (a • (1 : ℝ)) (1 : ℝ) := by
      rw [inner_smul_right]
    _ = b * (a * inner ℝ (1 : ℝ) (1 : ℝ)) := by
      rw [inner_smul_left]
      simp
    _ = a * b := by rw [hOneInner]; ring

/-- The ambient endpoint-pair Wilson kernel is symmetric under exchanging the
source and target endpoint pairs.  This is inherited componentwise from the
symmetric one-slab Wilson kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_representative_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealL2KernelRepresentativeSymmetric
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta) := by
  intro p
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.2.1 p.1.1 *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.2.2 p.1.2 =
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1.1 p.2.1 *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1.2 p.2.2
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
      H N hN beta hbeta p.2.1 p.1.1,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
      H N hN beta hbeta p.2.2 p.1.2]

/-- Pairing the ambient pair kernel against an arbitrary test vector in the
outer coordinate and the shorter recursive Haar message in the inner
coordinate gives exactly the Hilbert inner product with the `R+2` message.
This is the quotient-level Fubini bridge needed for the operator recursion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_pairing_test_recursiveMessage_eq_inner_add_two
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta)
        g
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H (R + 2) N hN beta hbeta)
        g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta
  let msg :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
      H R N hN beta hbeta
  let plus :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
      H (R + 2) N hN beta hbeta
  have hMsgProd :
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        msg p.2) =ᵐ[μ.prod μ]
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
          H R N beta p.2) := by
    exact
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq
        (by simpa [msg, μ] using
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_coeFn
            H R N hN beta hbeta))
  have hRawEq :
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        inner ℝ (K p) (realL2ExternalTensor g msg p)) =ᵐ[μ.prod μ]
      (fun p =>
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta p *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta p.2) * g p.1) := by
    filter_upwards [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta,
      realL2ExternalTensor_coeFn g msg,
      hMsgProd] with p hK hTensor hMsg
    simp only [realL2ExternalTensorFunction] at hTensor
    rw [hK, hTensor, hMsg,
      positiveHalfFixedAmbientRecursiveOperator_real_inner_eq_mul]
    ring
  have hRaw : Integrable
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta p *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta p.2) * g p.1)
      (μ.prod μ) :=
    Integrable.congr
      (MeasureTheory.L2.integrable_inner K (realL2ExternalTensor g msg)) hRawEq
  calc
    realL2HilbertSchmidtKernelPairing K g msg =
        inner ℝ K (realL2ExternalTensor g msg) := rfl
    _ = ∫ p, inner ℝ (K p) (realL2ExternalTensor g msg p) ∂(μ.prod μ) :=
      MeasureTheory.L2.inner_def K (realL2ExternalTensor g msg)
    _ = ∫ p,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta p *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta p.2) * g p.1
        ∂(μ.prod μ) :=
      integral_congr_ae hRawEq
    _ = ∫ outer, ∫ inner,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta inner) * g outer
        ∂μ ∂μ := by
      exact MeasureTheory.integral_prod _ hRaw
    _ = ∫ outer,
        (∫ inner,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (outer, inner) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
              H R N beta inner
          ∂μ) * g outer
        ∂μ := by
      apply integral_congr_ae
      filter_upwards with outer
      rw [integral_mul_const]
    _ = ∫ outer,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H (R + 2) N beta outer * g outer
        ∂μ := by
      apply integral_congr_ae
      filter_upwards with outer
      rw [
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_add_two_eq_pairKernel_message_integral
          H R N hN beta hbeta outer]
    _ = inner ℝ plus g := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_coeFn
          H (R + 2) N hN beta hbeta] with outer hPlus
      rw [hPlus, positiveHalfFixedAmbientRecursiveOperator_real_inner_eq_mul]
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H (R + 2) N hN beta hbeta) g := by
      rfl

/-- Exact fixed-ambient transfer recursion in the common pair-Haar Hilbert
space.  Peeling two inward slices is exactly one application of the ambient
pair transfer operator; the ambient spatial extent `H` is unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_eq_pairTransferOperator
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R + 2) N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta
  let msg :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
      H R N hN beta hbeta
  let plus :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
      H (R + 2) N hN beta hbeta
  let rhs :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta msg
  have hSymm : RealL2HilbertSchmidtKernelPairingSymmetric K :=
    realL2HilbertSchmidtKernelPairing_symmetric_of_ae_symmetric_rep
      K
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta)
      (by simpa [K, μ] using
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
          H N hN beta hbeta))
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_representative_symmetric
        H N hN beta hbeta)
  have hCoeff : ∀ g : Lp ℝ 2 μ, inner ℝ plus g = inner ℝ rhs g := by
    intro g
    calc
      inner ℝ plus g = realL2HilbertSchmidtKernelPairing K g msg := by
        symm
        simpa [K, msg, plus, μ] using
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_pairing_test_recursiveMessage_eq_inner_add_two
            H R N hN beta hbeta g)
      _ = realL2HilbertSchmidtKernelPairing K msg g := hSymm g msg
      _ = inner ℝ rhs g := by
        symm
        simpa [K, msg, rhs, μ] using
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner
            H N hN beta hbeta msg g)
  have hzero : inner ℝ (plus - rhs) (plus - rhs) = 0 := by
    rw [inner_sub_left, hCoeff (plus - rhs)]
    simp
  have hsub : plus - rhs = 0 := (inner_self_eq_zero.mp hzero)
  have hEq : plus = rhs := sub_eq_zero.mp hsub
  simpa [plus, rhs, msg, μ] using hEq

end

end MathlibAnalytic
end MGAP4D
