import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalReferenceIntegratedVarianceParallelogram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitProductFiberMass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-BL: actual Wilson outer-Haar fiber-variance measurability

BK proves the nonnegative outer integral of the Haar-fiber parallelogram
given precise AEMeasurable hypotheses. BL discharges them using the
ACTUAL concrete original Wilson joint observable and the existing
jointly a.e.-measurable ORIGINAL ground-state split density.

The mean of a jointly measurable real family is measurable by mathlib's
StronglyMeasurable.integral_prod_right', and the centered squared norm
has measurable ENNReal section integral by
Measurable.lintegral_prod_right'. The genuine original ground-state
fiber mass has an a.e.-measurable outer representative by the existing
Wilson split-density integration theorem.

No new probability law, fiber mass floor, projection commutativity or
new beta cutoff is introduced. The source remains literal original
mass-weighted physical Wilson right one-link Haar reference.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Measurability of parameterized extended-real variance on an s-finite
fiber, without imposing an unjustified arbitrary-context integrability
or independence hypothesis. -/
theorem p4Q2BL_evariance_outer_measurable
    {Outer SU : Type*}
    [MeasurableSpace Outer] [MeasurableSpace SU]
    (μHaar : Measure SU) [SFinite μHaar]
    (F : Outer × SU → ℝ) (hF : StronglyMeasurable F) :
    Measurable (fun ctx : Outer =>
      evariance (fun u : SU => F (ctx, u)) μHaar) := by
  let mean : Outer → ℝ := fun ctx => ∫ u, F (ctx, u) ∂μHaar
  have hMean : StronglyMeasurable mean := hF.integral_prod_right'
  have hCentered :
      Measurable (fun p : Outer × SU => F p - mean p.1) :=
    hF.measurable.sub (hMean.measurable.comp measurable_fst)
  have hSquared :
      Measurable (fun p : Outer × SU => ‖F p - mean p.1‖ₑ ^ 2) :=
    hCentered.enorm.pow_const _
  have hIntegral :
      Measurable (fun ctx : Outer =>
        ∫⁻ u : SU, ‖F (ctx, u) - mean ctx‖ₑ ^ 2 ∂μHaar) :=
    hSquared.lintegral_prod_right'
  simpa only [ProbabilityTheory.evariance, mean] using hIntegral

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "SU" => Matrix.specialUnitaryGroup (Fin N) ℂ
/-- The literal left-boundary × off-target right-Haar outer carrier. -/
abbrev p4Q2BL_originalOuterType
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- The real joint observable induces a genuinely jointly measurable
Haar section over the actual original left/off-target context × SU(N).
This is stronger than separately measurable fixed-context sections. -/
theorem p4Q2BL_originalJointOneLink_section_joint_stronglyMeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (fun z : p4Q2BL_originalOuterType H N target × SU =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F z.1.1 z.1.2 z.2) := by
  let eSplit :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := SU) target
  let eEval :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := SU) target
  have hLeft : Measurable (fun z : p4Q2BL_originalOuterType H N target × SU => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hRight :
      Measurable (fun z : p4Q2BL_originalOuterType H N target × SU =>
        eSplit.symm (eEval.symm z.2, z.1.2)) :=
    eSplit.symm.measurable.comp
      ((eEval.symm.measurable.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
  have hAssemble :
      Measurable (fun z : p4Q2BL_originalOuterType H N target × SU =>
        (z.1.1, eSplit.symm (eEval.symm z.2, z.1.2))) :=
    hLeft.prodMk hRight
  have hStrong :
      StronglyMeasurable (fun z : p4Q2BL_originalOuterType H N target × SU =>
        F (z.1.1, eSplit.symm (eEval.symm z.2, z.1.2))) :=
    hF.comp_measurable hAssemble
  change StronglyMeasurable (fun z : p4Q2BL_originalOuterType H N target × SU =>
    F (z.1.1, eSplit.symm (eEval.symm z.2, z.1.2)))
  exact hStrong

/-- Fiber Haar variance of a strongly measurable original Wilson joint
observable is measurable in the original left/off-target configuration. -/
theorem p4Q2BL_originalJointOneLinkHaarVariance_measurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    Measurable (fun ctx : p4Q2BL_originalOuterType H N target =>
      evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F ctx.1 ctx.2)
        (normalizedCompactHaar SU)) := by
  let μLink : Measure SU := normalizedCompactHaar SU
  letI : IsProbabilityMeasure μLink := by
    dsimp [μLink]
    infer_instance
  have hjoint :=
    p4Q2BL_originalJointOneLink_section_joint_stronglyMeasurable
      H N target F hF
  simpa only [μLink] using
    (p4Q2BL_evariance_outer_measurable μLink
      (fun z : p4Q2BL_originalOuterType H N target × SU =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F z.1.1 z.1.2 z.2) hjoint)

/-- A.e. measurability of the LITERAL ORIGINAL physical Wilson
ground-state one-link outer fiber mass; this is the old jointly measurable
split density integrated over the selected target Haar coordinate. -/
theorem p4Q2BL_originalGroundStateOuterMass_aemeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    AEMeasurable
      (fun ctx : p4Q2BL_originalOuterType H N target =>
        periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
          H N hN beta hbeta target ctx)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi (fun _ :
          PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar SU))) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar SU)
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar SU)
  have hw :
      AEMeasurable
        (fun z :
            (p4Q2BL_originalOuterType H N target) ×
              (PeriodicHypercubicEvenSpatialSliceTargetLink H target → SU) =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta z.1.1 target (z.2, z.1.2))
        ((μ.prod μOff).prod μTarget) := by
    simpa [μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
        H N hN beta hbeta target)
  have hZ :
      AEMeasurable
        (fun ctx : p4Q2BL_originalOuterType H N target =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta ctx.1 target ctx.2)
        (μ.prod μOff) := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass]
      using hw.lintegral_prod_right'
  simpa [μ, μOff,
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass] using hZ

/-- Measurability premise of BK for the ORIGINAL mass and exp(-32β)
weighted right-target Haar variance, for every strongly measurable
concrete Wilson joint observable. No β cutoff or mass floor. -/
theorem p4Q2BL_originalJointHaarReferenceIntegrand_aemeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    AEMeasurable
      (fun ctx : p4Q2BL_originalOuterType H N target =>
        (periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
          H N hN beta hbeta target ctx *
          ENNReal.ofReal (Real.exp (-32 * beta))) *
        evariance
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F ctx.1 ctx.2)
          (normalizedCompactHaar SU))
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi (fun _ :
          PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar SU))) := by
  let μOuter : Measure (p4Q2BL_originalOuterType H N target) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ :
        PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar SU))
  have hm :=
    p4Q2BL_originalGroundStateOuterMass_aemeasurable
      H N hN beta hbeta target
  have hv :=
    p4Q2BL_originalJointOneLinkHaarVariance_measurable
      H N target F hF
  change AEMeasurable
    (fun ctx : p4Q2BL_originalOuterType H N target =>
      (periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
        H N hN beta hbeta target ctx *
        ENNReal.ofReal (Real.exp (-32 * beta))) *
      evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F ctx.1 ctx.2)
        (normalizedCompactHaar SU)) μOuter
  exact (hm.mul aemeasurable_const).mul hv.aemeasurable

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
