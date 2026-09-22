import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionBetaContinuity

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance fixedRightResponseBetaSmokeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

-- The law, its boundary, and the observable vary through an arbitrary parameter space.
example {P : Type*} [TopologicalSpace P] (H N : ℕ) (hN : 0 < N)
    (beta : P → Set.Ici (0 : ℝ))
    (C : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hbeta : Continuous beta) (hC : Continuous C)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => ∫ A, f p A ∂
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
        H N hN (beta p).1 (beta p).2 (C p))) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_integral_continuous_param
    H N hN beta C f hbeta hC hf

-- No response-continuity hypothesis, remote-pair restriction, or positive-beta restriction.
example {P : Type*} [TopologicalSpace P] (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : P → Set.Ici (0 : ℝ))
    (B : P → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k : P → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hbeta : Continuous beta) (hB : Continuous B)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hh : Continuous h) (hk : Continuous k) :
    Continuous (fun p =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN (beta p).1 (beta p).2 (B p) target source (g₁ p) (g₂ p) (h p) (k p)) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_continuous_param
    H N hN target source beta B g₁ g₂ h k hbeta hB hg₁ hg₂ hh hk

-- The exact compact test variables used by the canonical supremum all move jointly.
example (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ))) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN p.1.1 p.1.2 p.2.1 target source
        p.2.2.1.1 p.2.2.1.2 p.2.2.2.1 p.2.2.2.2) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_joint_continuous
    H N hN target source

-- The half-line endpoint beta = 0 is included, even when target = source.
example (H N : ℕ) (hN : 0 < N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ContinuousAt (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta.1 beta.2 B target target g₁ g₂ h k)
      ⟨0, le_rfl⟩ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_continuous_param
    H N hN target target (fun beta => beta) (fun _ => B)
    (fun _ => g₁) (fun _ => g₂) (fun _ => h) (fun _ => k)
    continuous_id continuous_const continuous_const continuous_const
    continuous_const continuous_const).continuousAt

end

end MGAP4D.MathlibAnalytic
