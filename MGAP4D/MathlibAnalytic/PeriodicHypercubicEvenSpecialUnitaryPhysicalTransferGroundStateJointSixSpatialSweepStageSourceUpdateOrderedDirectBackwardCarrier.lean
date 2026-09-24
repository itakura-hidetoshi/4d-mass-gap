import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateBackwardDirectFiberEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateDirectEnergyFubini
import Mathlib.Tactic

/-!
# Connect the ordered direct energy to the reversible backward carrier

PR #4730 identifies the physical source-pair direct-energy average with the
ordered law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

PR #4734 defines the forward/backward source direct fiber energies on the
reversible target heat-bath joint law.

This file connects them exactly.  The nonnegative ordered square is expanded by
Tonelli, the source/target fiber integrals are exchanged, and the target fiber
sample is reinserted as the full target heat-bath transition.  No real-integral
Fubini obligation is introduced in this change of coordinates.

The final statement is

  ofReal(orderedDirectAverage)
    = lintegral backwardDirectFiberEnergy dJ_target.

No source/target commutation or influence estimate is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance orderedDirectBackwardCarrierSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance orderedDirectBackwardCarrierSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance orderedDirectBackwardCarrierSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance orderedDirectBackwardCarrierSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance orderedDirectBackwardCarrierSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance orderedDirectBackwardCarrierSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Updates at two distinct spatial links commute pointwise. -/
theorem periodicHypercubicEvenSpatialSliceUpdate_comm_of_ne
    {H : ℕ}
    {Gauge : Type}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (C : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (g v : Gauge) :
    Function.update (Function.update C source v) target g =
      Function.update (Function.update C target g) source v := by
  funext e
  by_cases hs : e = source
  · subst e
    simp [Function.update, Ne.symm hne]
  · by_cases ht : e = target
    · subst e
      simp [Function.update, hne]
    · simp [Function.update, hs, ht]

/-- The ordered direct square is exactly the full-configuration source-update
square on the target-updated background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_eq_sourceSquare_after_targetUpdate
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (v g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left C v g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifferenceSquare
        H N source F left (Function.update C target g) v := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_eq_fullUpdates]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifferenceSquare
  rw [
    periodicHypercubicEvenSpatialSliceUpdate_comm_of_ne
      target source hne C g v]

/-- ENNReal form of the ordered direct average from PR #4729. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ∫⁻ Cvg,
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂

/-- For bounded concrete representatives, ofReal of the real ordered average is
exactly its ENNReal lower-integral presentation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy_ofReal_eq_ennreal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
          H N hN beta hbeta target source F left B distinguishedSource k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal
        H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  let square :=
    fun Cvg :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2
  have hInt : Integrable square μ := by
    simpa [square, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_integrable
        H N hN beta hbeta target source F hF bound hbound
        left B distinguishedSource k g₂
  have hNonneg : ∀ᵐ Cvg ∂μ, 0 ≤ square Cvg :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal
  simpa [square, μ] using
    (ofReal_integral_eq_lintegral_ofReal hInt hNonneg)

/-- The ENNReal ordered direct average is the forward source direct fiber
energy averaged over the actual target heat-bath old/new joint law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal_eq_forwardHeatBathJoint
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal
        H N hN beta hbeta target source F left B distinguishedSource k g₂ =
      ∫⁻ CD,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateForwardDirectFiberEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  let κs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂
  let κt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource target k g₂
  let sourceBG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let targetKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
      H N hN beta hbeta B distinguishedSource source target k g₂
  let ordered :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  let J :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
  let square :=
    fun Cvg :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
          H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2)
  let forward :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateForwardDirectFiberEnergy
      H N hN beta hbeta source F left B distinguishedSource k g₂
  let targetInt := fun Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
    ∫⁻ g, square (Cv, g) ∂targetKernel Cv
  have hSquareReal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_stronglyMeasurable
      H N target source F hF left
  have hSquare : Measurable square := by
    simpa [square] using hSquareReal.measurable.ennreal_ofReal
  have hTargetInt : Measurable targetInt := by
    dsimp [targetInt]
    exact hSquare.lintegral_kernel_prod_right'
  have hForward :
      Measurable forward := by
    simpa [forward] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateForwardDirectFiberEnergy_measurable
        H N hN beta hbeta source F hF left B distinguishedSource k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  have hOrderedFubini :
      (∫⁻ Cvg, square Cvg ∂ordered) =
        ∫⁻ Cv, targetInt Cv ∂sourceBG := by
    unfold ordered
    simpa [targetInt] using Measure.lintegral_compProd hSquare
  have hSourceFubini :
      (∫⁻ Cv, targetInt Cv ∂sourceBG) =
        ∫⁻ C, ∫⁻ v, targetInt (C, v) ∂κs C ∂μ := by
    unfold sourceBG
    simpa [κs, μ] using Measure.lintegral_compProd hTargetInt
  have hSwap :
      (∫⁻ C, ∫⁻ v, targetInt (C, v) ∂κs C ∂μ) =
        ∫⁻ C, ∫⁻ g,
          ∫⁻ v, square ((C, v), g) ∂κs C ∂κt C ∂μ := by
    apply lintegral_congr
    intro C
    calc
      (∫⁻ v, targetInt (C, v) ∂κs C) =
          ∫⁻ v, ∫⁻ g, square ((C, v), g) ∂κt C ∂κs C := by
        apply lintegral_congr
        intro v
        dsimp [targetInt]
        rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel_apply,
          ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
            H N hN beta hbeta B source distinguishedSource target k g₂ C]
      _ = ∫⁻ g, ∫⁻ v, square ((C, v), g) ∂κs C ∂κt C := by
        have hSection :
            Measurable
              (fun vg :
                Matrix.specialUnitaryGroup (Fin N) ℂ ×
                  Matrix.specialUnitaryGroup (Fin N) ℂ =>
                square ((C, vg.1), vg.2)) :=
          hSquare.comp
            ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
        exact lintegral_lintegral_swap hSection.aemeasurable
  have hSquareToForward :
      (∫⁻ C, ∫⁻ g,
          ∫⁻ v, square ((C, v), g) ∂κs C ∂κt C ∂μ) =
        ∫⁻ C, ∫⁻ g,
          forward (C, Function.update C target g) ∂κt C ∂μ := by
    apply lintegral_congr
    intro C
    apply lintegral_congr
    intro g
    dsimp [forward]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateForwardDirectFiberEnergy
    apply lintegral_congr
    intro v
    dsimp [square]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_eq_sourceSquare_after_targetUpdate
        H N target source hne F left C v g]
  have hTargetPush :
      (∫⁻ C, ∫⁻ g,
          forward (C, Function.update C target g) ∂κt C ∂μ) =
        ∫⁻ C, ∫⁻ D,
          forward (C, D)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B source distinguishedSource target k g₂ C
          ∂μ := by
    apply lintegral_congr
    intro C
    have hSection :
        Measurable
          (fun D :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            forward (C, D)) :=
      hForward.comp (measurable_const.prodMk measurable_id)
    have hUpdate :
        Measurable
          (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
            Function.update C target g) :=
      measurable_update C
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map
        H N hN beta hbeta B source distinguishedSource target k g₂ C,
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
        H N hN beta hbeta B source distinguishedSource target k g₂ C]
    exact (MeasureTheory.lintegral_map hSection hUpdate).symm
  have hJointFubini :
      (∫⁻ C, ∫⁻ D,
          forward (C, D)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B source distinguishedSource target k g₂ C
          ∂μ) =
        ∫⁻ CD, forward CD ∂J := by
    unfold J
    symm
    exact Measure.lintegral_compProd hForward
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal
  change (∫⁻ Cvg, square Cvg ∂ordered) = ∫⁻ CD, forward CD ∂J
  calc
    (∫⁻ Cvg, square Cvg ∂ordered) =
        ∫⁻ Cv, targetInt Cv ∂sourceBG := hOrderedFubini
    _ = ∫⁻ C, ∫⁻ v, targetInt (C, v) ∂κs C ∂μ := hSourceFubini
    _ = ∫⁻ C, ∫⁻ g,
          ∫⁻ v, square ((C, v), g) ∂κs C ∂κt C ∂μ := hSwap
    _ = ∫⁻ C, ∫⁻ g,
          forward (C, Function.update C target g) ∂κt C ∂μ := hSquareToForward
    _ = ∫⁻ C, ∫⁻ D,
          forward (C, D)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B source distinguishedSource target k g₂ C
          ∂μ := hTargetPush
    _ = ∫⁻ CD, forward CD ∂J := hJointFubini

/-- Final backward-coordinate representation of the real ordered direct
average. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy_ofReal_eq_backwardHeatBathJoint
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
          H N hN beta hbeta target source F left B distinguishedSource k g₂) =
      ∫⁻ CD,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ := by
  calc
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
          H N hN beta hbeta target source F left B distinguishedSource k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal
        H N hN beta hbeta target source F left B distinguishedSource k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy_ofReal_eq_ennreal
        H N hN beta hbeta target source F hF bound hbound
        left B distinguishedSource k g₂
    _ = ∫⁻ CD,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateForwardDirectFiberEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergyENNReal_eq_forwardHeatBathJoint
        H N hN beta hbeta target source hne F hF
        left B distinguishedSource k g₂
    _ = ∫⁻ CD,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdate_directFiberEnergy_heatBathJoint_lintegral_forward_eq_backward
        H N hN beta hbeta target source F hF
        left B distinguishedSource k g₂

end

end MGAP4D.MathlibAnalytic
