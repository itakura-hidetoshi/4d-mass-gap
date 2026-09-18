import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedRightTargetRatioCrossRatioResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Updating the same right-boundary target twice makes the second exact local
Boltzmann factor the quotient of the two factors computed from the original
base.  This is the exact multiplicative cocycle needed to turn the canonical
vacuum update expectation into a target-ratio expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_same_eq_div
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A (Function.update B target g₂) target g₁ =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂ := by
  have hK₂ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta A B target g₂
  have hK₁ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta A B target g₁
  have hK₂₁ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta A (Function.update B target g₂) target g₁
  have hUpdate :
      Function.update (Function.update B target g₂) target g₁ =
        Function.update B target g₁ := by
    funext e
    by_cases he : e = target <;> simp [he]
  rw [hUpdate, hK₁, hK₂] at hK₂₁
  have hKPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta A B
  have hL₂Pos :
      0 <
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta A B target g₂
  apply (eq_div_iff (ne_of_gt hL₂Pos)).2
  nlinarith

/-- The literal fixed-right target-factor ratio has the matching
volume-independent lower Harnack bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-16 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂ := by
  have hDenPos :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta A B target g₂
  apply (le_div_iff₀ hDenPos).2
  calc
    Real.exp (-16 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂ ≤
      Real.exp (-16 * beta) * Real.exp (8 * beta) := by
        exact mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
            H N hN beta hbeta A B target g₂)
          (Real.exp_pos _).le
    _ = Real.exp (-8 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g₁ :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
        H N hN beta hbeta A B target g₁

/-- Every probability average of the fixed-right target ratio inherits the
same lower Harnack bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    [IsProbabilityMeasure μ] :
    Real.exp (-16 * beta) ≤
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂μ := by
  have hConst :
      Integrable
        (fun _ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          Real.exp (-16 * beta)) μ :=
    integrable_const _
  have hRatio :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_integrable
      H N hN beta hbeta B target g₁ g₂ μ
  calc
    Real.exp (-16 * beta) =
        ∫ _ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          Real.exp (-16 * beta) ∂μ := by simp
    _ ≤
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂μ := by
      exact integral_mono hConst hRatio
        (Filter.Eventually.of_forall fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
            H N hN beta hbeta A B target g₁ g₂)

/-- For a spatially remote source, the fixed-right target-ratio expectation is
exactly the corresponding ratio of canonical continuous-vacuum values. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_integral_eq_vacuum_ratio_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (s g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source s) target g₂)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source s) target g₁) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source s) target g₂) := by
  let Bs : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B source s
  let C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update Bs target g₂
  have hVac :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_rightTargetLocalFactor_eq_vacuum_update_ratio
      H N hN beta hbeta C target g₁
  have hUpdate :
      Function.update C target g₁ =
        Function.update (Function.update B source s) target g₁ := by
    funext e
    by_cases he : e = target <;> simp [C, Bs, he]
  rw [hUpdate] at hVac
  have hIntegrand :
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂) =
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A C target g₁) := by
    funext A
    symm
    calc
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A C target g₁ =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A Bs target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A Bs target g₂ := by
            simpa [C] using
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_same_eq_div
                H N beta A Bs target g₁ g₂
      _ =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂ := by
            rw [
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
                H N beta A B target source s g₁ (Ne.symm hne) hNoShare,
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
                H N beta A B target source s g₂ (Ne.symm hne) hNoShare]
  rw [hIntegrand]
  simpa [C, Bs] using hVac

/-- The actual remote canonical-vacuum cross ratio is exactly the quotient of
the two fixed-right target-ratio expectations.  This is the normalization
identity needed before any residual estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_eq_fixedRightTargetRatio_expectation_ratio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₁) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) /
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₁) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) =
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) /
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_integral_eq_vacuum_ratio_of_remote
      H N hN beta hbeta B hne hNoShare h g₁ g₂,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_integral_eq_vacuum_ratio_of_remote
      H N hN beta hbeta B hne hNoShare k g₁ g₂]
  have hh₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (Function.update (Function.update B source h) target g₁)
  have hh₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (Function.update (Function.update B source h) target g₂)
  have hk₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₁)
  have hk₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  field_simp [ne_of_gt hh₁, ne_of_gt hh₂, ne_of_gt hk₁, ne_of_gt hk₂]
  ring

/-- The actual remote canonical-vacuum cross ratio is at most one plus the
fixed-right response residual multiplied by the volume-independent local
Harnack constant.  No target cardinality factor is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_le_one_add_exp_sixteen_mul_fixedRightTargetRatioResponseAbs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₁) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) /
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₁) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) ≤
      1 + Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k := by
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source h) target g₂)
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
  let Eh : ℝ := ∫ A, F A ∂μh
  let Ek : ℝ := ∫ A, F A ∂μk
  let R : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source g₁ g₂ h k
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source h) target g₂)
  letI : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)
  have hEkLower : Real.exp (-16 * beta) ≤ Ek := by
    simpa [Ek, F, μk] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le_integral
        H N hN beta hbeta B target g₁ g₂ μk
  have hEkPos : 0 < Ek := lt_of_lt_of_le (Real.exp_pos _) hEkLower
  have hScale : 1 ≤ Real.exp (16 * beta) * Ek := by
    calc
      1 = Real.exp (16 * beta) * Real.exp (-16 * beta) := by
        rw [← Real.exp_add]
        norm_num
      _ ≤ Real.exp (16 * beta) * Ek := by
        exact mul_le_mul_of_nonneg_left hEkLower (Real.exp_pos _).le
  have hR : R = |Eh - Ek| := by
    rfl
  have hDiff : Eh - Ek ≤ R := by
    rw [hR]
    exact le_abs_self (Eh - Ek)
  have hRNonneg : 0 ≤ R := by
    rw [hR]
    exact abs_nonneg _
  have hRScale : R ≤ Real.exp (16 * beta) * R * Ek := by
    calc
      R = R * 1 := by ring
      _ ≤ R * (Real.exp (16 * beta) * Ek) :=
        mul_le_mul_of_nonneg_left hScale hRNonneg
      _ = Real.exp (16 * beta) * R * Ek := by ring
  have hRatio :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_eq_fixedRightTargetRatio_expectation_ratio
      H N hN beta hbeta B hne hNoShare h k g₁ g₂
  change
    _ ≤ 1 + Real.exp (16 * beta) * R
  rw [hRatio]
  change Eh / Ek ≤ 1 + Real.exp (16 * beta) * R
  apply (div_le_iff₀ hEkPos).2
  nlinarith

end

end MathlibAnalytic
end MGAP4D
