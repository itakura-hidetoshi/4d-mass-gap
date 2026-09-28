import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectVarianceDiagonalResidual
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-!
# Backward direct variance on the target heat-bath joint carrier

PR #4869 gives the pointwise Harnack comparison

  ofReal V(C, C[target <- g])
    <= K(beta) * ofReal V(C,C),

where `V` is the backward source direct centered variance and

  K(beta) = (exp (32 beta))^2.

PR #4872 identifies the diagonal term exactly with the genuine source
one-link heat-bath projection residual.

This file first exposes the missing measurable-carrier fact for `V`, then
integrates the pointwise Harnack comparison against the actual target
heat-bath old/new joint law.  The target fiber is integrated out exactly,
leaving the source reference law and the genuine source residual.

No target/source cardinality factor, triangle inequality, factor two,
response symmetry, or additional comparison coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardDirectVarianceJointResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardDirectVarianceJointResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardDirectVarianceJointResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardDirectVarianceJointResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardDirectVarianceJointResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardDirectVarianceJointResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The backward direct mean is strongly measurable in the old/new background
pair.  The observable is read from the first background while the source
conditional kernel is based at the second background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
        H N hN beta hbeta source F left B distinguishedSource k g₂) := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂
  let κPair :
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    κ.comap Prod.snd measurable_snd
  let X :=
    fun z :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
        H N source F left z.1.1 z.2
  have hUpdate :
      Measurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update z.1.1 source z.2) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N source).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hFirst :
      StronglyMeasurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, z.1.1)) :=
    hF.comp_measurable
      (measurable_const.prodMk (measurable_fst.comp measurable_fst))
  have hSecond :
      StronglyMeasurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, Function.update z.1.1 source z.2)) :=
    hF.comp_measurable (measurable_const.prodMk hUpdate)
  have hX : StronglyMeasurable X := by
    simpa [
      X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
      using hFirst.sub hSecond
  have hIntegral :
      StronglyMeasurable
        (fun CD =>
          ∫ v, X (CD, v) ∂κPair CD) :=
    hX.integral_kernel_prod_right'
  simpa [
    κ, κPair, X,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean]
    using hIntegral

/-- The centered backward direct variance is strongly measurable in the
old/new background pair. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
        H N hN beta hbeta source F left B distinguishedSource k g₂) := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂
  let κPair :
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    κ.comap Prod.snd measurable_snd
  let X :=
    fun z :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
        H N source F left z.1.1 z.2
  let m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
      H N hN beta hbeta source F left B distinguishedSource k g₂
  have hUpdate :
      Measurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update z.1.1 source z.2) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N source).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hFirst :
      StronglyMeasurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, z.1.1)) :=
    hF.comp_measurable
      (measurable_const.prodMk (measurable_fst.comp measurable_fst))
  have hSecond :
      StronglyMeasurable
        (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, Function.update z.1.1 source z.2)) :=
    hF.comp_measurable (measurable_const.prodMk hUpdate)
  have hX : StronglyMeasurable X := by
    simpa [
      X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
      using hFirst.sub hSecond
  have hm :
      StronglyMeasurable m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean_stronglyMeasurable
      H N hN beta hbeta source F hF left B distinguishedSource k g₂
  have hCentered :
      StronglyMeasurable
        (fun z =>
          (X z - m z.1) ^ 2) :=
    (hX.sub (hm.comp_measurable measurable_fst)).pow 2
  have hIntegral :
      StronglyMeasurable
        (fun CD =>
          ∫ v, (X (CD, v) - m CD) ^ 2 ∂κPair CD) :=
    hCentered.integral_kernel_prod_right'
  simpa [
    κ, κPair, X, m,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy]
    using hIntegral

/-- Integrating the pointwise #4869 Harnack comparison over the actual target
heat-bath old/new joint law leaves only the diagonal source variance.  PR #4872
then identifies that diagonal average exactly with the genuine source
heat-bath projection residual energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_heatBathJoint_lintegral_le_harnackLawFactor_mul_referenceSourceResidual_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ CD,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ∫⁻ C,
          ENNReal.ofReal
            ((F (left, C) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                  H N hN beta hbeta B source distinguishedSource source k g₂
                  (fun D => F (left, D)) C) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  let κt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B source distinguishedSource target k g₂
  let J :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
      H N hN beta hbeta source F left B distinguishedSource k g₂
  let K : ℝ≥0∞ := ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)
  let diag : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C => ENNReal.ofReal (V (C, C))
  have hVReal : StronglyMeasurable V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_stronglyMeasurable
      H N hN beta hbeta source F hF left B distinguishedSource k g₂
  have hV : Measurable (fun CD => ENNReal.ofReal (V CD)) :=
    hVReal.measurable.ennreal_ofReal
  have hDiag : Measurable diag := by
    exact hV.comp (measurable_id.prodMk measurable_id)
  have hFubini :
      (∫⁻ CD, ENNReal.ofReal (V CD) ∂J) =
        ∫⁻ C, ∫⁻ D, ENNReal.ofReal (V (C, D)) ∂κt C ∂μ := by
    unfold J
    simpa [μ, κt] using Measure.lintegral_compProd hV
  have hInner :
      ∀ C,
        (∫⁻ D, ENNReal.ofReal (V (C, D)) ∂κt C) ≤
          K * diag C := by
    intro C
    have hSection : Measurable (fun D => ENNReal.ofReal (V (C, D))) :=
      hV.comp (measurable_const.prodMk measurable_id)
    have hUpdate :
        Measurable
          (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
            Function.update C target g) :=
      measurable_update C
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map
        H N hN beta hbeta B source distinguishedSource target k g₂ C]
    calc
      (∫⁻ D, ENNReal.ofReal (V (C, D))
        ∂Measure.map
          (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
            Function.update C target g)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂ C)) =
        ∫⁻ g,
          ENNReal.ofReal (V (C, Function.update C target g))
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂ C :=
        MeasureTheory.lintegral_map hSection hUpdate
      _ ≤
        ∫⁻ _g,
          K * diag C
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂ C := by
        apply lintegral_mono
        intro g
        simpa [V, K, diag] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_targetUpdate_ofReal_le_harnackLawFactor_mul_diagonal_of_bounded
            H N hN beta hbeta source target hne
            F hF bound hbound left B C distinguishedSource k g₂ g
      _ = K * diag C := by
        simp
  have hJoint :
      (∫⁻ CD, ENNReal.ofReal (V CD) ∂J) ≤
        K * ∫⁻ C, diag C ∂μ := by
    calc
      (∫⁻ CD, ENNReal.ofReal (V CD) ∂J) =
          ∫⁻ C, ∫⁻ D, ENNReal.ofReal (V (C, D)) ∂κt C ∂μ :=
        hFubini
      _ ≤ ∫⁻ C, K * diag C ∂μ :=
        lintegral_mono hInner
      _ = K * ∫⁻ C, diag C ∂μ := by
        rw [lintegral_const_mul']
        simp [K]
  have hDiagResidual :
      (∫⁻ C, diag C ∂μ) =
        ∫⁻ C,
          ENNReal.ofReal
            ((F (left, C) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                  H N hN beta hbeta B source distinguishedSource source k g₂
                  (fun D => F (left, D)) C) ^ 2)
          ∂μ := by
    simpa [diag, V, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_diagonal_reference_lintegral_eq_referenceSourceResidual_sq_lintegral_of_bounded
        H N hN beta hbeta B distinguishedSource source k g₂
        F hF bound hbound left
  calc
    (∫⁻ CD, ENNReal.ofReal (V CD) ∂J) ≤
        K * ∫⁻ C, diag C ∂μ :=
      hJoint
    _ =
      K *
        ∫⁻ C,
          ENNReal.ofReal
            ((F (left, C) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                  H N hN beta hbeta B source distinguishedSource source k g₂
                  (fun D => F (left, D)) C) ^ 2)
          ∂μ := by
      rw [hDiagResidual]
    _ =
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ∫⁻ C,
          ENNReal.ofReal
            ((F (left, C) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                  H N hN beta hbeta B source distinguishedSource source k g₂
                  (fun D => F (left, D)) C) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource k g₂ := by
      rfl

end

end MGAP4D.MathlibAnalytic
