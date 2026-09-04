import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepMessage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance positiveHalfInnerMessagePairTransferIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfInnerMessagePairTransferCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfInnerMessagePairTransferSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfInnerMessagePairTransferMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfInnerMessagePairTransferBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfInnerMessagePairTransferSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

local instance positiveHalfInnerMessagePairTransferPairHaarSFinite (M N : ℕ) :
    SFinite
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The erased first/last-slab Wilson product is continuous on complete path
space.  It is a finite product of continuous one-slab kernels, over exactly the
slabs retained by the Markov remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel_continuous
    (M N : ℕ)
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
        (M + 2) N beta) := by
  classical
  let I := Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (M + 2))
  let Path :=
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N
  let factor : I → Path → ℝ := fun i path =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel (M + 2) N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)
  have hFactor : ∀ i : I, Continuous (factor i) := by
    intro i
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        (M + 2) N beta).comp₂
        (continuous_apply i.castSucc)
        (continuous_apply i.succ)
  have hProd : ∀ s : Finset I,
      Continuous (fun path : Path => s.prod (fun i => factor i path)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (continuous_const : Continuous (fun _ : Path => (1 : ℝ)))
    | @insert a s ha ih =>
        simpa [Finset.prod_insert, ha] using (hFactor a).mul ih
  let s : Finset I :=
    ((Finset.univ.erase
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex (M + 2))).erase
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex (M + 2)))
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
  change Continuous (fun path : Path => s.prod (fun i => factor i path))
  exact hProd s

/-- The three-factor-coordinate interior remainder is measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel_measurable
    (M N : ℕ)
    (beta : ℝ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
        M N beta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
  exact
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel_continuous
      M N beta).measurable.comp
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
        M N).symm.measurable

/-- After outer-pair independence has been proved, the residual kernel on
`innerPair × deep` is measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel_measurable
    (M N : ℕ)
    (beta : ℝ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
        M N beta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
  exact
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel_measurable
      M N beta).comp
      (measurable_const.prodMk measurable_id)

/-- Uniform Wilson bound for the erased interior slab product. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel_abs_le_one
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
        (M + 2) N beta path| ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro i hi
    exact abs_nonneg _
  · intro i hi
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        (M + 2) N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)

/-- The outer-independent residual kernel remains pointwise bounded by one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel_abs_le_one
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (rest :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
        M N beta rest| ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel_abs_le_one
      M N hN beta hbeta _

/-- The inward message obtained by deep-Haar integration is strongly measurable
on pair-Haar space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_stronglyMeasurable
    (M N : ℕ)
    (beta : ℝ) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
        M N beta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
  exact
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel_measurable
      M N beta).stronglyMeasurable.integral_prod_right'

/-- The inward message is uniformly bounded by one, because the deep law is a
probability measure and the residual Wilson product has absolute value at most
one pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_abs_le_one
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (inner :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
        M N beta inner| ≤ 1 := by
  let μDeep :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N
  letI : IsFiniteMeasure μDeep := by infer_instance
  have h := norm_integral_le_of_norm_le_const
    (μ := μDeep)
    (f := fun deep =>
      periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
        M N beta (inner, deep))
    (C := 1)
    (Filter.Eventually.of_forall fun deep => by
      simpa [Real.norm_eq_abs] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel_abs_le_one
          M N hN beta hbeta (inner, deep))
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage,
    μDeep, Real.norm_eq_abs] using h

/-- The inward Wilson message belongs to pair-Haar `L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_memLp_two
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
        M N beta)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  exact MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_stronglyMeasurable
      M N beta).aestronglyMeasurable
    1
    (Filter.Eventually.of_forall fun inner => by
      simpa [Real.norm_eq_abs] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_abs_le_one
          M N hN beta hbeta inner)

/-- Canonical pair-Haar `L²` vector of the inward Wilson message. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_memLp_two
    M N hN beta hbeta).toLp
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage M N beta)

/-- The inward-message `L²` vector has the literal deep-Haar message as its a.e.
representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2_coeFn
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (fun inner =>
      periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
        M N hN beta hbeta inner) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N]
      periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage M N beta :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_memLp_two
    M N hN beta hbeta).coeFn_toLp

/-- The constant-one outer state belongs to pair-Haar `L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPairHaarOne_memLp_two
    (M N : ℕ) :
    MemLp
      (fun _ :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N => (1 : ℝ))
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N
  letI : IsFiniteMeasure μ := by infer_instance
  exact MemLp.of_bound aestronglyMeasurable_const 1
    (Filter.Eventually.of_forall fun _ => by norm_num)

/-- Canonical constant-one vector in pair-Haar `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPairHaarOneL2
    (M N : ℕ) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) :=
  (periodicHypercubicEvenSpecialUnitaryPairHaarOne_memLp_two M N).toLp
    (fun _ => (1 : ℝ))

/-- The constant-one `L²` vector is represented by literal one a.e. -/
theorem periodicHypercubicEvenSpecialUnitaryPairHaarOneL2_coeFn
    (M N : ℕ) :
    (fun outer => periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N outer) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N]
      (fun _ => (1 : ℝ)) :=
  (periodicHypercubicEvenSpecialUnitaryPairHaarOne_memLp_two M N).coeFn_toLp

/-- The literal pair kernel multiplied by the inward message is integrable on
pair-Haar × pair-Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_mul_innerMessage_integrable
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta p *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta p.2)
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N
  letI : IsFiniteMeasure (μ.prod μ) := by infer_instance
  have hMeas : AEStronglyMeasurable
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta p *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta p.2)
      (μ.prod μ) := by
    simpa [μ] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_aestronglyMeasurable
        (M + 2) N beta).mul
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_stronglyMeasurable
          M N beta).aestronglyMeasurable.comp_snd)
  exact Integrable.of_bound hMeas 1
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta p| *
            |periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
              M N beta p.2| ≤ 1 * 1 := by
          exact mul_le_mul
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
              (M + 2) N hN beta hbeta p)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage_abs_le_one
              M N hN beta hbeta p.2)
            (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num)

/-- The representative-level outer/inner double integral is exactly the
Hilbert--Schmidt kernel pairing of the ambient one-slab pair kernel against the
constant outer state and the inward message. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_pairing_one_innerMessage
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          (M + 2) N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
          M N hN beta hbeta) =
      ∫ outer, ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta inner
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      (M + 2) N hN beta hbeta
  let one := periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N
  let msg :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
      M N hN beta hbeta
  have hOneProd :
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) =>
        one p.1) =ᵐ[μ.prod μ] (fun _ => (1 : ℝ)) := by
    exact
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq
        (by simpa [one, μ] using
          (periodicHypercubicEvenSpecialUnitaryPairHaarOneL2_coeFn M N))
  have hMsgProd :
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) =>
        msg p.2) =ᵐ[μ.prod μ]
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
          M N beta p.2) := by
    exact
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq
        (by simpa [msg, μ] using
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2_coeFn
            M N hN beta hbeta))
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_mul_innerMessage_integrable
      M N hN beta hbeta
  calc
    realL2HilbertSchmidtKernelPairing K one msg =
        inner ℝ K (realL2ExternalTensor one msg) := rfl
    _ = ∫ p, inner ℝ (K p) (realL2ExternalTensor one msg p) ∂(μ.prod μ) :=
      MeasureTheory.L2.inner_def K (realL2ExternalTensor one msg)
    _ = ∫ p,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta p *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta p.2
        ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
          (M + 2) N hN beta hbeta,
        realL2ExternalTensor_coeFn one msg,
        hOneProd,
        hMsgProd] with p hK hTensor hOne hMsg
      simp only [realL2ExternalTensorFunction] at hTensor
      rw [hK, hTensor, hOne, hMsg]
      have hOneInner : inner ℝ (1 : ℝ) (1 : ℝ) = 1 := by
        have h := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (1 : ℝ)
        norm_num at h ⊢
        exact h.symm
      have hRealInner (a b : ℝ) : inner ℝ a b = a * b := by
        calc
          inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
          _ = b * inner ℝ (a • (1 : ℝ)) (1 : ℝ) := by
            rw [inner_smul_right]
          _ = b * (a * inner ℝ (1 : ℝ) (1 : ℝ)) := by
            rw [inner_smul_left]
            simp
          _ = a * b := by rw [hOneInner]; ring
      simp [hRealInner]
    _ = ∫ outer, ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta inner
        ∂μ ∂μ := by
      exact MeasureTheory.integral_prod _ (by simpa [μ] using hRaw)
    _ = ∫ outer, ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta inner
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
      rfl

/-- Operator-level receiving theorem: the complete nondegenerate positive-half
Wilson path-Haar amplitude is exactly a matrix coefficient of the already
constructed ambient pair-Haar Hilbert--Schmidt one-step transfer operator,
with constant outer state and the canonically integrated inward Wilson message. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_pairTransferOperator_inner
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          (M + 2) N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N))
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
          M N hN beta hbeta) := by
  calc
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
      ∫ outer, ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta inner
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_outer_inner_message
        M N hN beta hbeta
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          (M + 2) N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
          M N hN beta hbeta) :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_pairing_one_innerMessage
        M N hN beta hbeta).symm
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          (M + 2) N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N))
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
          M N hN beta hbeta) := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner
          (M + 2) N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPairHaarOneL2 M N)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessageL2
            M N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D