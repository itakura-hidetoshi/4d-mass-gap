import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionBetaContinuity

/-!
# Joint continuity of the literal fixed-right target-ratio response

Transport the existing normalized kernel law along an arbitrary continuous
parameter map, allowing the observable to depend on extra test variables.
Recover the literal local factor from the positive Wilson-kernel update identity.
The existing response is the absolute difference of two such expectations.

No continuous choice, remote-pair restriction, positive-beta restriction, uniform
mass floor, or response-continuity input is introduced. The canonical supremum
profile is not redefined. Local instances have explicit module-specific names.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

/-- Reindex before specializing the weight to the concrete Wilson construction.
This opaque boundary prevents elaboration from repeatedly unfolding the vacuum. -/
private theorem fixedRightResponse_weightedProbability_integral_pullback
    {P Q X : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (w : Q → X → ℝ) (f : P → X → ℝ) (c : P → Q)
    (hw : Continuous (Function.uncurry w))
    (hf : Continuous (Function.uncurry f)) (hc : Continuous c)
    (hwNonneg : ∀ q x, 0 ≤ w q x)
    (hMassPos : ∀ q, 0 < ∫ x, w q x ∂mu) :
    Continuous (fun p => ∫ x, f p x ∂realIntegralWeightedProbabilityMeasure mu (w (c p))) := by
  have hPull : Continuous (fun q : P × X => w (c q.1) q.2) :=
    hw.comp ((hc.comp continuous_fst).prodMk continuous_snd)
  exact realIntegralWeightedProbabilityMeasure_integral_continuous mu
    (fun p => w (c p)) f hPull hf
    (fun p x => hwNonneg (c p) x) (fun p => hMassPos (c p))

local instance fixedRightResponseBetaContinuitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance fixedRightResponseBetaContinuitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance fixedRightResponseBetaContinuitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance fixedRightResponseBetaContinuitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance fixedRightResponseBetaContinuitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance fixedRightResponseBetaContinuitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- The actual positive mass is inherited under full-boundary integration only. -/
private theorem fixedRightResponse_continuousWeight_integral_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < ∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  calc
    0 < ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta C A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta C
    _ = _ := integral_congr_ae
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_eq_continuousWeight
        H N hN beta hbeta C)

/-- Both the boundary law and the observable may depend on an arbitrary
parameter space. The original positive normalization integral is retained. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_continuous_param
    {P : Type*} [TopologicalSpace P] (H N : ℕ) (hN : 0 < N)
    (beta : P → Set.Ici (0 : ℝ))
    (C : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hbeta : Continuous beta) (hC : Continuous C)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => ∫ A, f p A ∂
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN (beta p).1 (beta p).2 (C p))) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
  exact fixedRightResponse_weightedProbability_integral_pullback
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun q : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN q.1.1 q.1.2 q.2)
    f (fun p => (beta p, C p))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_beta_joint_continuous
      H N hN)
    hf (hbeta.prodMk hC)
    (fun q A => (mul_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN q.1.1 q.1.2 A)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N q.1.1 A q.2)).le)
    (fun q => fixedRightResponse_continuousWeight_integral_pos H N hN q.1.1 q.1.2 q.2)

/-- The same arbitrary-parameter theorem for the original L2-presented law,
transferred by exact measure equality without evaluating an L2 class at a point. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_integral_continuous_param
    {P : Type*} [TopologicalSpace P] (H N : ℕ) (hN : 0 < N)
    (beta : P → Set.Ici (0 : ℝ))
    (C : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hbeta : Continuous beta) (hC : Continuous C)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => ∫ A, f p A ∂
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
        H N hN (beta p).1 (beta p).2 (C p))) := by
  have heq :
      (fun p => ∫ A, f p A ∂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
          H N hN (beta p).1 (beta p).2 (C p))) =
      (fun p => ∫ A, f p A ∂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN (beta p).1 (beta p).2 (C p))) := by
    funext p
    exact congrArg
      (fun nu : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        ∫ A, f p A ∂nu)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
        H N hN (beta p).1 (beta p).2 (C p))
  exact Eq.mpr (congrArg (fun g : P → ℝ => Continuous g) heq)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_continuous_param
      H N hN beta C f hbeta hC hf)

/-- Updating a fixed coordinate is continuous in both configuration and value. -/
private theorem fixedRightResponse_update_continuous
    {P : Type*} [TopologicalSpace P] (H N : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (B : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : P → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hB : Continuous B) (hg : Continuous g) :
    Continuous (fun p => Function.update (B p) e (g p)) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i = e
  · subst i
    simpa only [Function.update_self] using hg
  · simpa only [Function.update_of_ne hi] using (continuous_apply i).comp hB

/-- Recover the existing local factor as a quotient of the positive literal
Wilson kernels. This avoids re-expanding its finite local-action formula. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_param
    {P : Type*} [TopologicalSpace P] (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : P → ℝ)
    (A B : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : P → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hbeta : Continuous beta) (hA : Continuous A) (hB : Continuous B)
    (hg : Continuous g) :
    Continuous (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N (beta p) (A p) (B p) target (g p)) := by
  have hUpdate := fixedRightResponse_update_continuous H N target B g hB hg
  have hNum : Continuous (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N (beta p) (A p) (Function.update (B p) target (g p))) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous H N).comp
      (hbeta.prodMk (hA.prodMk hUpdate))
  have hDen : Continuous (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N (beta p) (A p) (B p)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous H N).comp
      (hbeta.prodMk (hA.prodMk hB))
  have hRatio := hNum.div hDen (fun p =>
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N (beta p) (A p) (B p)).ne')
  have heq :
      (fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N (beta p) (A p) (B p) target (g p)) =
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N (beta p) (A p) (Function.update (B p) target (g p)) /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N (beta p) (A p) (B p)) := by
    funext p
    apply (eq_div_iff
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N (beta p) (A p) (B p)).ne').2
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N (beta p) (A p) (B p) target (g p)).symm
  exact Eq.mpr (congrArg (fun f : P → ℝ => Continuous f) heq) hRatio

/-- Continuity of the actual response along arbitrary continuous choices of
its input parameters, not an assumption of continuity on a response witness. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_continuous_param
    {P : Type*} [TopologicalSpace P] (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : P → Set.Ici (0 : ℝ))
    (B : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k : P → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hbeta : Continuous beta) (hB : Continuous B)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hh : Continuous h) (hk : Continuous k) :
    Continuous (fun p =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN (beta p).1 (beta p).2 (B p) target source (g₁ p) (g₂ p) (h p) (k p)) := by
  let F : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun p A =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N (beta p).1 A (B p) target (g₁ p) /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N (beta p).1 A (B p) target (g₂ p)
  have hNum : Continuous
      (fun q : P × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N (beta q.1).1 q.2 (B q.1) target (g₁ q.1)) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_param
      (P := P × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      H N target (fun q => (beta q.1).1) (fun q => q.2)
      (fun q => B q.1) (fun q => g₁ q.1)
      (continuous_subtype_val.comp (hbeta.comp continuous_fst)) continuous_snd
      (hB.comp continuous_fst) (hg₁.comp continuous_fst)
  have hDen : Continuous
      (fun q : P × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N (beta q.1).1 q.2 (B q.1) target (g₂ q.1)) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_param
      (P := P × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      H N target (fun q => (beta q.1).1) (fun q => q.2)
      (fun q => B q.1) (fun q => g₂ q.1)
      (continuous_subtype_val.comp (hbeta.comp continuous_fst)) continuous_snd
      (hB.comp continuous_fst) (hg₂.comp continuous_fst)
  have hF : Continuous (Function.uncurry F) := hNum.div hDen (fun q =>
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N (beta q.1).1 q.2 (B q.1) target (g₂ q.1)).ne')
  have hCh := fixedRightResponse_update_continuous H N target
    (fun p => Function.update (B p) source (h p)) g₂
    (fixedRightResponse_update_continuous H N source B h hB hh) hg₂
  have hCk := fixedRightResponse_update_continuous H N target
    (fun p => Function.update (B p) source (k p)) g₂
    (fixedRightResponse_update_continuous H N source B k hB hk) hg₂
  have hEh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_continuous_param
      H N hN beta (fun p => Function.update (Function.update (B p) source (h p)) target (g₂ p))
      F hbeta hCh hF
  have hEk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_continuous_param
      H N hN beta (fun p => Function.update (Function.update (B p) source (k p)) target (g₂ p))
      F hbeta hCk hF
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
  exact (hEh.sub hEk).abs

/-- The full product-domain statement needed before taking the canonical
supremum over the compact configuration and four group-valued test variables. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_joint_continuous
    (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ))) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN p.1.1 p.1.2 p.2.1 target source
        p.2.2.1.1 p.2.2.1.2 p.2.2.2.1 p.2.2.2.2) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_continuous_param
      (P := Set.Ici (0 : ℝ) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ))))
      H N hN target source (fun p => p.1) (fun p => p.2.1)
      (fun p => p.2.2.1.1) (fun p => p.2.2.1.2)
      (fun p => p.2.2.2.1) (fun p => p.2.2.2.2)
      continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_fst.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      (continuous_snd.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))

end

end MGAP4D.MathlibAnalytic
