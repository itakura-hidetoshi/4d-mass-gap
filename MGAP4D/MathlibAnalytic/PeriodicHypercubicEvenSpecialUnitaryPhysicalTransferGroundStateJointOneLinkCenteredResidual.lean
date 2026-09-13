import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkIntegratedVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointOneLinkCenteredResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateJointOneLinkCenteredResidualTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance groundStateJointOneLinkCenteredResidualTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- On a concrete good outer context, the actual normalized singleton-target
fiber variance is bounded by the squared residual around any chosen real
center.  This is the projection-minimality inequality needed before inserting
an off-target-measurable representative of the genuine joint `condExpL2`.

The proof transports `L²` membership from the direct one-link normalized fiber
to the literal split target fiber, so no pointwise representative of a joint
`L²` quotient is used here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_evariance_le_centeredSquaredResidual_of_map_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hmap :
      Measure.map
          (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta left
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
            H N target retained) target)
    (hprob : IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
        H N hN beta hbeta left target retained))
    (c : ℝ) :
    evariance
        (fun targetCfg =>
          X (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target retained) ≤
      doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target retained)
        (fun targetCfg =>
          X (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
        c := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
      H N hN beta hbeta left target retained
  let right := periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    H N target retained
  let νDirect :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
      H N hN beta hbeta left right target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using hprob
  have heval : MeasurePreserving eval ν νDirect := by
    refine ⟨eval.measurable, ?_⟩
    simpa [ν, νDirect, right, eval] using hmap
  have hXDirect : MemLp X 2 νDirect := by
    simpa [νDirect, right] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_memLp_two
        H N hN beta hbeta left right target X hX
  have hXActual : MemLp (fun targetCfg => X (eval targetCfg)) 2 ν :=
    hXDirect.comp_measurePreserving heval
  simpa [ν, eval] using
    (evariance_le_doobCenteredSquaredResidual
      ν (fun targetCfg => X (eval targetCfg)) hXActual c)

/-- For almost every outer context, the actual singleton-target variance is no
larger than the squared residual around an arbitrary context-dependent center.
The center may depend on the complete left boundary and every retained
right-boundary coordinate, but not on the target link itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_context_evariance_le_centeredSquaredResidual_ae
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hX :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
          MemLp (X left retained) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        evariance
            (fun targetCfg =>
              X left retained
                (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) ≤
          doobCenteredSquaredResidual
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained)
            (fun targetCfg =>
              X left retained
                (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
            (C left retained) := by
  have hmap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target
  have hprob :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_isProbabilityMeasure
      H N hN beta hbeta target
  filter_upwards [hX, hmap, hprob] with left hXLeft hmapLeft hprobLeft
  filter_upwards [hXLeft, hmapLeft, hprobLeft] with retained hX' hmap' hprob'
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_evariance_le_centeredSquaredResidual_of_map_eq
      H N hN beta hbeta target left retained (X left retained) hX' hmap' hprob'
      (C left retained)

/-- The actual singleton-target fiber variance remains below every
context-centered squared residual after multiplication by the exact target
fiber mass and iterated integration over the complete outer context. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_context_evariance_weighted_lintegral_le_centeredSquaredResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hX :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
          MemLp (X left retained) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (∫⁻ left,
      ∫⁻ retained,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
              H N hN beta hbeta left target retained *
            evariance
              (fun targetCfg =>
                X left retained
                  (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
                H N hN beta hbeta left target retained)
          ∂(Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
      (∫⁻ left,
        ∫⁻ retained,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained *
              doobCenteredSquaredResidual
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
                  H N hN beta hbeta left target retained)
                (fun targetCfg =>
                  X left retained
                    (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
                (C left retained)
            ∂(Measure.pi
              (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  have hres :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_context_evariance_le_centeredSquaredResidual_ae
      H N hN beta hbeta target X C hX
  refine lintegral_mono_ae ?_
  filter_upwards [hres] with left hleft
  refine lintegral_mono_ae ?_
  filter_upwards [hleft] with retained hretained
  exact mul_le_mul_left'
    hretained
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
      H N hN beta hbeta left target retained)

/-- Sharp Haar one-link variance, weighted by the exact ground-state target
fiber mass, is bounded by the actual-fiber squared residual around every
outer-context center.  The only distortion is the already-proved
`exp (-16 * beta)` one-link coefficient; no additional Harnack loss is
introduced by centering or integration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_context_haar_evariance_weighted_lintegral_le_centeredSquaredResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hX :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
          MemLp (X left retained) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (∫⁻ left,
      ∫⁻ retained,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
              H N hN beta hbeta left target retained *
            ((ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
              evariance (X left retained)
                (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
          ∂(Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
      (∫⁻ left,
        ∫⁻ retained,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained *
              doobCenteredSquaredResidual
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
                  H N hN beta hbeta left target retained)
                (fun targetCfg =>
                  X left retained
                    (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
                (C left retained)
            ∂(Measure.pi
              (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_context_evariance_weighted_lintegral_lower_bound
      H N hN beta hbeta target X hX).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_context_evariance_weighted_lintegral_le_centeredSquaredResidual
        H N hN beta hbeta target X C hX)

end

end MathlibAnalytic
end MGAP4D
