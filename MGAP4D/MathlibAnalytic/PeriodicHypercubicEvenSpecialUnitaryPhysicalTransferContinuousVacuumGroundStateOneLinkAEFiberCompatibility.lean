import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectNormalizedFiberBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance continuousVacuumGroundStateAEFiberCompatibilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumGroundStateAEFiberCompatibilitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumGroundStateAEFiberCompatibilitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumGroundStateAEFiberCompatibilitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumGroundStateAEFiberCompatibilitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumGroundStateAEFiberCompatibilitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance continuousVacuumGroundStateAEFiberCompatibilityTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance continuousVacuumGroundStateAEFiberCompatibilityTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- A canonical complete right-boundary configuration reconstructed from the
off-target coordinates by inserting the identity at the selected target.
Only the retained coordinates matter to every normalized target fiber below. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
    ((fun _ => 1), retained)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction_rightFromOffTarget
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSliceOffTargetRestriction target
      (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
        H N target retained) = retained := by
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let right := periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    H N target retained
  have hsnd := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd
    target right
  change (split right).2 =
    periodicHypercubicEvenSpatialSliceOffTargetRestriction target right at hsnd
  have hsplit : split right = ((fun _ => 1), retained) := by
    exact split.apply_symm_apply _
  rw [hsplit] at hsnd
  exact hsnd.symm

/-- Pull the sharp continuous-vacuum direct normalized one-link law back to the
canonical singleton-target coordinate. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained)
        target
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))

/-- For Haar-a.e. left boundary and Haar-a.e. retained off-target context, the
legacy joint-density target fiber and the canonical continuous-vacuum target
fiber define exactly the same normalized measure.

The equality is deliberately only almost everywhere in the outer context:
the old joint density uses an arbitrary `L²` representative, whereas the new
fiber uses the canonical continuous representative.  No exceptional fiber is
promoted to a pointwise statement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_eq_continuousVacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let omegaC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let omega := fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 B
  have hOmega : omegaC =ᵐ[μ] omega := by
    simpa [μ, omegaC, omega] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
        H N hN beta hbeta)
  have hsplit : MeasurePreserving split μ (μTarget.prod μOff) := by
    simpa [split, μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
        H N target)
  have hsplitInv : MeasurePreserving split.symm (μTarget.prod μOff) μ :=
    hsplit.symm
  have hOmegaSplit :
      ∀ᵐ z ∂(μTarget.prod μOff), omegaC (split.symm z) = omega (split.symm z) :=
    hsplitInv.quasiMeasurePreserving.ae hOmega
  have hOmegaSwap :
      ∀ᵐ z ∂(μOff.prod μTarget), omegaC (split.symm z.swap) = omega (split.symm z.swap) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hOmegaSplit
  have hOmegaSections :
      ∀ᵐ retained ∂μOff, ∀ᵐ targetCfg ∂μTarget,
        omegaC (split.symm (targetCfg, retained)) =
          omega (split.symm (targetCfg, retained)) := by
    simpa [Prod.swap] using Measure.ae_ae_of_ae_prod hOmegaSwap
  filter_upwards [hOmega, hOmegaSections] with left hleft hsections
  filter_upwards [hsections] with retained hright
  let right := periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    H N target retained
  let wOld := fun targetCfg :
      PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
      H N hN beta hbeta left target (targetCfg, retained)
  let wNew := fun targetCfg :
      PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target (eval targetCfg)
  have hWeight : wOld =ᵐ[μTarget] wNew := by
    filter_upwards [hright] with targetCfg htarget
    have hOff :
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = retained := by
      simpa [right] using
        periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction_rightFromOffTarget
          H N target retained
    have hUpdate :
        Function.update right target (eval targetCfg) =
          split.symm (targetCfg, retained) := by
      have h :=
        periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update
          target right targetCfg
      rw [hOff] at h
      simpa [eval] using h.symm
    change wOld targetCfg = wNew targetCfg
    rw [show wOld targetCfg =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target (eval targetCfg) by
      dsimp [wOld]
      rw [← hOff]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_offTargetRestriction_eq_directFiberWeight
          H N hN beta hbeta left right target targetCfg]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
    rw [hUpdate]
    rw [← hleft, ← htarget]
    rfl
  have hMassEq : doobWeightMass μTarget wOld = doobWeightMass μTarget wNew := by
    simpa [doobWeightMass] using lintegral_congr_ae hWeight
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure
  change doobWeightedMeasure μTarget wOld = doobWeightedMeasure μTarget wNew
  unfold doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards [hWeight] with targetCfg htarget
  simp only [doobWeightedDensity]
  rw [htarget, hMassEq]

/-- Evaluation of the singleton target coordinate transports the continuous
split fiber exactly back to the sharp direct normalized `SU(N)` one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure_map_targetEvaluation_eq_direct
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target retained) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained) target := by
  classical
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μGroup := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let right := periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    H N target retained
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  have hevalEval :
      MeasurePreserving
        (Function.eval
          (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
        μTarget μGroup := by
    simpa [μTarget, μGroup] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target => μGroup)
        (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
  have heval : MeasurePreserving eval μTarget μGroup := by
    have hfun :
        (eval :
          (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =
        Function.eval
          (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target) := by
      funext targetCfg
      simp [eval]
    rw [hfun]
    exact hevalEval
  have hMass :
      doobWeightMass μTarget (fun targetCfg => w (eval targetCfg)) =
        doobWeightMass μGroup w := by
    simpa [doobWeightMass] using
      heval.lintegral_comp_emb eval.measurableEmbedding w
  ext s hs
  rw [Measure.map_apply eval.measurable hs]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
    doobWeightedMeasure
  rw [withDensity_apply _ (hs.preimage eval.measurable)]
  rw [withDensity_apply _ hs]
  unfold doobWeightedDensity
  change
    (∫⁻ targetCfg in eval ⁻¹' s,
      w (eval targetCfg) / doobWeightMass μTarget (fun targetCfg => w (eval targetCfg))
      ∂μTarget) =
      ∫⁻ g in s, w g / doobWeightMass μGroup w ∂μGroup
  rw [hMass]
  exact
    heval.setLIntegral_comp_preimage_emb eval.measurableEmbedding
      (fun g => w g / doobWeightMass μGroup w) s

/-- Consequently the actual split ground-state Markov fiber, after singleton
coordinate evaluation, agrees almost everywhere in its outer context with the
sharp continuous-vacuum normalized direct one-link law.  This is the precise
compatibility needed before transferring the sharp variance estimate into the
genuine joint conditional-expectation hierarchy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        Measure.map
            (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
            H N hN beta hbeta left
            (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
              H N target retained) target := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_eq_continuousVacuum
      H N hN beta hbeta target] with left hleft
  filter_upwards [hleft] with retained hretained
  rw [hretained]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateRightJointSplitTargetNormalizedFiberMeasure_map_targetEvaluation_eq_direct
      H N hN beta hbeta left target retained

end

end MathlibAnalytic
end MGAP4D
