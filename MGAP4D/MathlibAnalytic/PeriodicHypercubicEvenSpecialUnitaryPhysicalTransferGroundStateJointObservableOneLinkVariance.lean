import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkContextVarianceTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointObservableOneLinkVarianceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointObservableOneLinkVarianceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointObservableOneLinkVarianceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointObservableOneLinkVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointObservableOneLinkVarianceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointObservableOneLinkVarianceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateJointObservableOneLinkVarianceTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance groundStateJointObservableOneLinkVarianceTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- The sharp actual split-fiber variance estimate applied to a genuine
pointwise observable on the two-boundary ground-state configuration space.
For each outer context, the direct `SU(N)` section is obtained by inserting the
single target value through the canonical singleton-coordinate equivalence.

The bounded strongly-measurable core assumption supplies `L²(Haar)` for every
one-link section without choosing or evaluating an arbitrary `L²` quotient
representative.  The exact coefficient remains `exp (-16 * beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointObservable_splitTarget_evariance_lower_bound_ae
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable (Function.uncurry f))
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ left right, |f left right| ≤ M) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
            evariance
              (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
                f left
                  ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                    ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
                      retained)))
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
          evariance
            (fun targetCfg =>
              f left
                ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                  (targetCfg, retained)))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) := by
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let X := fun
      (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
      (g : Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    f left (split.symm (eval.symm g, retained))
  have hXLp : ∀ left retained,
      MemLp (X left retained) 2
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
    intro left retained
    have hcoord : Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          (left, split.symm (eval.symm g, retained))) := by
      fun_prop
    have hStrong : StronglyMeasurable (X left retained) := by
      simpa [X, Function.uncurry] using hf.comp_measurable hcoord
    have hConst : MemLp
        (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => M) 2
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
      memLp_const M
    apply hConst.of_le hStrong.aestronglyMeasurable
    filter_upwards [] with g
    simpa [X, Real.norm_eq_abs, abs_of_nonneg hM0] using
      hM left (split.symm (eval.symm g, retained))
  have hXLpAE :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
          MemLp (X left retained) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
    filter_upwards [] with left
    filter_upwards [] with retained
    exact hXLp left retained
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_context_evariance_lower_bound_ae
      H N hN beta hbeta target X hXLpAE
  filter_upwards [h] with left hleft
  filter_upwards [hleft] with retained hretained
  have hfiber :
      (fun targetCfg => X left retained (eval targetCfg)) =
        (fun targetCfg => f left (split.symm (targetCfg, retained))) := by
    funext targetCfg
    change
      f left (split.symm (eval.symm (eval targetCfg), retained)) =
        f left (split.symm (targetCfg, retained))
    rw [eval.symm_apply_apply]
  rw [hfiber] at hretained
  simpa [X, split, eval] using hretained

end

end MathlibAnalytic
end MGAP4D
