import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectVarianceJointResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteBackgroundUpdateRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepGate
import Mathlib.Tactic

/-!
# Absorb the pure backward source-law response

PR #4736 splits the backward direct mean exactly as

  BackwardDirectMean(C,D)
    = DiagonalLocalMean(C) + BackwardLawResponse(C,D).

PRs #4872--#4873 close the centered-variance branch of the backward direct
fiber energy.  The remaining source-law response compares the source
conditional law based at C with the source conditional law based at the
target-updated background D.

This file uses the already-existing generic background-update centered-RMS
theorem with the correct reference anchor

  distinguishedTarget = fiber = source,
  backgroundFiber = target.

The center is chosen to be the diagonal source mean.  Therefore the two RMS
energies are

  V_diag

and

  V_cross + BackwardLawResponse^2.

This yields a scalar self-absorption inequality.  On the existing strict
physical-sweep interval the Harnack RMS coefficient eta(beta) is strictly
below one, so the response square is bounded by

  eta(beta)^2 / (1 - eta(beta)^2) * (V_diag + V_cross).

No finite-cardinality factor, source/target symmetry, arbitrary factor two,
or source-specific L2 identification is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardLawResponseAbsorptionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardLawResponseAbsorptionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardLawResponseAbsorptionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardLawResponseAbsorptionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardLawResponseAbsorptionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardLawResponseAbsorptionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Public probability-space Pythagoras around an arbitrary scalar center.
This is the public API form intentionally missing from the private local helper
used in PR #4868. -/
theorem
    probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq_of_memLp_two
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ x, (X x - c) ^ 2 ∂μ) =
      (∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ) +
        ((∫ y, X y ∂μ) - c) ^ 2 := by
  have hShift : MemLp (fun x => X x - c) 2 μ :=
    hX.sub (memLp_const c)
  have hXIntegrable : Integrable X μ :=
    hX.integrable one_le_two
  have hMeanShift :
      (∫ x, X x - c ∂μ) = (∫ x, X x ∂μ) - c := by
    rw [integral_sub hXIntegrable (integrable_const c)]
    simp
  have hVarShift :
      variance (fun x => X x - c) μ =
        (∫ x, (X x - c) ^ 2 ∂μ) -
          (∫ x, X x - c ∂μ) ^ 2 := by
    simpa only [Pi.pow_apply] using
      (variance_eq_sub hShift)
  have hVarInvariant :
      variance (fun x => X x - c) μ = variance X μ :=
    variance_sub_const hX.aestronglyMeasurable c
  have hVarBase :
      variance X μ =
        ∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ := by
    exact variance_eq_integral hX.aestronglyMeasurable.aemeasurable
  rw [hVarInvariant, hVarBase, hMeanShift] at hVarShift
  linarith

/-- Pure scalar absorption lemma. -/
theorem
    sq_le_eta_sq_div_one_sub_eta_sq_mul_add_of_abs_le_eta_mul_sqrt_add_add_sq
    (eta r a b : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta < 1)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (h :
      |r| ≤ eta * Real.sqrt (a + b + r ^ 2)) :
    r ^ 2 ≤
      (eta ^ 2 / (1 - eta ^ 2)) * (a + b) := by
  let q := Real.sqrt (a + b + r ^ 2)
  have hsum : 0 ≤ a + b + r ^ 2 := by
    nlinarith [sq_nonneg r]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.sqrt_nonneg _
  have hqSq : q ^ 2 = a + b + r ^ 2 := by
    dsimp [q]
    exact Real.sq_sqrt hsum
  have hmul :
      |r| * |r| ≤ (eta * q) * (eta * q) :=
    mul_le_mul h h (abs_nonneg r) (mul_nonneg heta0 hq0)
  have hsquare :
      r ^ 2 ≤ eta ^ 2 * q ^ 2 := by
    simpa [pow_two, sq_abs] using hmul
  rw [hqSq] at hsquare
  have hetaSqLt : eta ^ 2 < 1 := by
    nlinarith [sq_nonneg eta]
  have hden : 0 < 1 - eta ^ 2 :=
    sub_pos.mpr hetaSqLt
  have hcross :
      r ^ 2 * (1 - eta ^ 2) ≤ eta ^ 2 * (a + b) := by
    nlinarith
  have hdiv :
      r ^ 2 ≤
        (eta ^ 2 * (a + b)) / (1 - eta ^ 2) :=
    (le_div_iff₀ hden).2 hcross
  calc
    r ^ 2 ≤
        (eta ^ 2 * (a + b)) / (1 - eta ^ 2) := hdiv
    _ =
        (eta ^ 2 / (1 - eta ^ 2)) * (a + b) := by
      ring

/-- The local Harnack RMS coefficient is strictly below one throughout the
already-selected strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_lt_one_of_strictPhysicalSweepCutoff
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta < 1 := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRho0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
          s beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound_nonneg
      s beta hs hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
      s beta hbeta hcut
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
    at hGate
  nlinarith

/-- Absorption coefficient for the pure backward source-law response. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponseAbsorptionCoefficient
    (beta : ℝ) : ℝ :=
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  eta ^ 2 / (1 - eta ^ 2)

/-- Before scalar absorption, the pure source-law response is controlled by
the diagonal and cross centered variances plus its own squared gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_targetUpdate_abs_le_harnackInfluence_mul_sqrt_variances_add_self_of_bounded
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
    (left C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
        H N hN beta hbeta source F left B distinguishedSource k g₂
        (C, Function.update C target g)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta *
        Real.sqrt
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, C) +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, Function.update C target g) +
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, Function.update C target g)) ^ 2) := by
  let D := Function.update C target g
  let μC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  let μD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ D
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun v =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
        H N source F left C v
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
      H N hN beta hbeta source F left B distinguishedSource k g₂ C
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
      H N hN beta hbeta source F left B distinguishedSource k g₂ (C, D)
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
      H N hN beta hbeta source F left B distinguishedSource k g₂ (C, D)
  let center := F (left, C) - L
  let section : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N source F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction source C)
  letI : IsProbabilityMeasure μC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  letI : IsProbabilityMeasure μD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ D
  have hRight :
      StronglyMeasurable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          F (left, A)) :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hXStrong : StronglyMeasurable X := by
    dsimp [
      X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    exact
      stronglyMeasurable_const.sub
        (hRight.comp_measurable (measurable_update C))
  have hXBound : ∀ v, ‖X v‖ ≤ 2 * |bound| := by
    intro v
    have hFirst :
        |F (left, C)| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using
        (hbound (left, C)).trans (le_abs_self bound)
    have hSecond :
        |F (left, Function.update C source v)| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using
        (hbound (left, Function.update C source v)).trans (le_abs_self bound)
    rw [Real.norm_eq_abs]
    dsimp [
      X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    calc
      |F (left, C) - F (left, Function.update C source v)| ≤
          |F (left, C)| + |F (left, Function.update C source v)| :=
        abs_sub _ _
      _ ≤ |bound| + |bound| := add_le_add hFirst hSecond
      _ = 2 * |bound| := by ring
  have hXC : MemLp X 2 μC :=
    MemLp.of_bound hXStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hXBound)
  have hXD : MemLp X 2 μD :=
    MemLp.of_bound hXStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hXBound)
  have hMeanC : (∫ v, X v ∂μC) = L := by
    dsimp [X, μC, L]
    rw [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
        H N hN beta hbeta B source distinguishedSource source k g₂ C]
    rfl
  have hMeanD : (∫ v, X v ∂μD) = M := by
    dsimp [X, μD, M, D]
    rw [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
        H N hN beta hbeta B source distinguishedSource source k g₂
        (Function.update C target g)]
    rfl
  have hR : R = M - L := by
    rfl
  have hSection :
      ∀ v, section v - center = -(X v - L) := by
    intro v
    dsimp [section, center, X]
    rw [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update]
    ring
  have hSectionC :
      (∫ v, section v - center ∂μC) = 0 := by
    calc
      (∫ v, section v - center ∂μC) =
          ∫ v, -(X v - L) ∂μC := by
        apply integral_congr_ae
        filter_upwards with v
        exact hSection v
      _ = -(∫ v, X v - L ∂μC) := by
        rw [integral_neg]
      _ = 0 := by
        rw [integral_sub (hXC.integrable one_le_two) (integrable_const L)]
        rw [hMeanC]
        simp
  have hSectionD :
      (∫ v, section v - center ∂μD) = -R := by
    calc
      (∫ v, section v - center ∂μD) =
          ∫ v, -(X v - L) ∂μD := by
        apply integral_congr_ae
        filter_upwards with v
        exact hSection v
      _ = -(∫ v, X v - L ∂μD) := by
        rw [integral_neg]
      _ = -(M - L) := by
        rw [integral_sub (hXD.integrable one_le_two) (integrable_const L)]
        rw [hMeanD]
        simp
      _ = -R := by rw [hR]
  have hVarC :
      (∫ v, (X v - L) ^ 2 ∂μC) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) := by
    have hPyth :=
      probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq_of_memLp_two
        μC X hXC L
    rw [hMeanC] at hPyth
    have hDiagMean :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
            H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
          L := by
      have hSplit :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean_eq_local_add_lawResponse
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)
      simpa [L] using hSplit
    have hEnergy :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
          ∫ v, (X v - L) ^ 2 ∂μC := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply,
        hDiagMean]
      rfl
    exact hEnergy.symm
  have hVarD :
      (∫ v, (X v - L) ^ 2 ∂μD) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ (C, D) +
          R ^ 2 := by
    have hPyth :=
      probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq_of_memLp_two
        μD X hXD L
    rw [hMeanD] at hPyth
    have hEnergy :
        (∫ v, (X v - M) ^ 2 ∂μD) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ (C, D) := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
      rfl
    rw [hEnergy] at hPyth
    simpa [hR] using hPyth
  have hSectionEnergyC :
      (∫ v, (section v - center) ^ 2 ∂μC) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) := by
    calc
      (∫ v, (section v - center) ^ 2 ∂μC) =
          ∫ v, (X v - L) ^ 2 ∂μC := by
        apply integral_congr_ae
        filter_upwards with v
        rw [hSection v]
        ring
      _ = _ := hVarC
  have hSectionEnergyD :
      (∫ v, (section v - center) ^ 2 ∂μD) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ (C, D) +
          R ^ 2 := by
    calc
      (∫ v, (section v - center) ^ 2 ∂μD) =
          ∫ v, (X v - L) ^ 2 ∂μD := by
        apply integral_congr_ae
        filter_upwards with v
        rw [hSection v]
        ring
      _ = _ := hVarD
  have hRMS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy_of_bounded
      H N hN beta hbeta source F hF bound hbound
      left
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction source C)
      B C source distinguishedSource target hne
      k g₂ (C target) g center
  have hRMS' :
      |(∫ v, section v - center ∂μC) -
          (∫ v, section v - center ∂μD)| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
          Real.sqrt
            ((∫ v, (section v - center) ^ 2 ∂μC) +
              ∫ v, (section v - center) ^ 2 ∂μD) := by
    simpa [
      section, center, μC, μD, D,
      Function.update_eq_self target C] using hRMS
  calc
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
        H N hN beta hbeta source F left B distinguishedSource k g₂
        (C, Function.update C target g)| =
      |(∫ v, section v - center ∂μC) -
          (∫ v, section v - center ∂μD)| := by
        rw [hSectionC, hSectionD]
        simp [R, D]
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta *
        Real.sqrt
          ((∫ v, (section v - center) ^ 2 ∂μC) +
            ∫ v, (section v - center) ^ 2 ∂μD) := hRMS'
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta *
        Real.sqrt
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, C) +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, Function.update C target g) +
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, Function.update C target g)) ^ 2) := by
      rw [hSectionEnergyC, hSectionEnergyD]
      simp [R, D]
      ring_nf

/-- On the strict physical-sweep interval the pure source-law response square
is absorbed into the two centered backward variances. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_targetUpdate_sq_le_absorptionCoefficient_mul_variances_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
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
    (left C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
        H N hN beta hbeta source F left B distinguishedSource k g₂
        (C, Function.update C target g)) ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponseAbsorptionCoefficient
          beta *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂
            (C, C) +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂
            (C, Function.update C target g)) := by
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
      H N hN beta hbeta source F left B distinguishedSource k g₂
      (C, Function.update C target g)
  let a :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
      H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)
  let b :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
      H N hN beta hbeta source F left B distinguishedSource k g₂
      (C, Function.update C target g)
  have heta0 : 0 ≤ eta := by
    dsimp [eta]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
        beta hbeta
  have heta1 : eta < 1 := by
    dsimp [eta]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_lt_one_of_strictPhysicalSweepCutoff
        N hN s hs beta hbeta hcut
  have ha : 0 ≤ a := by
    dsimp [a]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_nonneg
        H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_nonneg
        H N hN beta hbeta source F left B distinguishedSource k g₂
        (C, Function.update C target g)
  have hRaw :
      |r| ≤ eta * Real.sqrt (a + b + r ^ 2) := by
    simpa [eta, r, a, b] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_targetUpdate_abs_le_harnackInfluence_mul_sqrt_variances_add_self_of_bounded
        H N hN beta hbeta B distinguishedSource source target hne
        k g₂ F hF bound hbound left C g
  have hAbsorb :=
    sq_le_eta_sq_div_one_sub_eta_sq_mul_add_of_abs_le_eta_mul_sqrt_add_add_sq
      eta r a b heta0 heta1 ha hb hRaw
  simpa [
    eta, r, a, b,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponseAbsorptionCoefficient] using
    hAbsorb

end

end MGAP4D.MathlibAnalytic
