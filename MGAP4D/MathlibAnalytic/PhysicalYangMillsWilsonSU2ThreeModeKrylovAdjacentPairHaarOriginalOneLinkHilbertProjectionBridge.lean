import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarIntegratedOriginalGroundStateOneLinkDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

/-!
# P4-Q2-AY: original Wilson one-link energy on the genuine physical Hilbert space

AX proved an actual Wilson ground-state mass-weighted, outer-product-Haar
one-link conditional-variance lower bound with coefficient exp(-32 beta).

The old canonical Markov disintegration has already identified its historical
target-link fiber variance (in iterated-integral presentation) with the squared
residual of the genuine physical joint-L2 conditional-expectation projection.

This unit connects these two exact presentations on a bounded continuous
one-link cylindrical core. Tonelli's inequality alone is enough in the needed
direction: an arbitrary nonnegative product integral never exceeds its
iterated integral. We do NOT silently assert product/iterated integral equality
without its a.e.-measurability premise.

In particular, no fictitious uniform lower bound on the original fiber mass,
no surrogate Wilson measure, no color independence, and no full-volume
transfer-operator spectral-gap statement are used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2600000
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

/-- Variance of a measurable real probe is invariant under the actual
measurable-equivalence pushforward, for any input measure. -/
theorem p4Q2AY_evariance_map_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (nu : Measure A) (e : A ≃ᵐ B) (X : B → ℝ)
    (hX : Measurable X) :
    evariance X (Measure.map e nu) = evariance (X ∘ e) nu := by
  let mu := Measure.map e nu
  have hid : IdentDistrib (e : A → B) id nu mu := by
    refine ⟨e.measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
    simp [mu]
  have hcomp := hid.comp_of_aemeasurable
    (hX.aemeasurable (μ := mu))
  have hvar := hcomp.evariance_eq
  simpa only [Function.comp_id] using hvar.symm

/-- An actual bounded continuous right-target Wilson observable on the
original complete left-right physical joint configuration carrier. -/
noncomputable def p4Q2AY_originalOneLinkJointProbe
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ :=
  fun z => X (z.2 target)

/-- The same original joint probe has a literal strongly measurable
representative, without evaluating any quotient-L2 vector pointwise. -/
theorem p4Q2AY_originalOneLinkJointProbe_stronglyMeasurable
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    StronglyMeasurable (p4Q2AY_originalOneLinkJointProbe H N target X) := by
  exact (X.continuous.measurable.comp
    ((measurable_pi_apply target).comp measurable_snd)).stronglyMeasurable

/-- The explicit uniform bound required by the existing real-L2 core. -/
theorem p4Q2AY_originalOneLinkJointProbe_norm_le
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖p4Q2AY_originalOneLinkJointProbe H N target X z‖ ≤ ‖X‖ :=
  X.norm_coe_le_norm (z.2 target)

/-- The genuine physical joint-L2 vector determined by the concrete Wilson
right-link observable. It uses the ORIGINAL ground-state joint probability. -/
noncomputable def p4Q2AY_originalOneLinkJointL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta (p4Q2AY_originalOneLinkJointProbe H N target X)
    (p4Q2AY_originalOneLinkJointProbe_stronglyMeasurable H N target X)
    ‖X‖ (p4Q2AY_originalOneLinkJointProbe_norm_le H N target X)

/-- The selected singleton-link coordinate of the reconstructed complete
right boundary equals exactly the input SU(N) link, for every context. -/
private theorem p4Q2AY_reconstruct_target
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
      ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g, retained))
      target = g := by
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have hs := congrArg (fun z =>
      z.1 (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
    (split.apply_symm_apply (eval.symm g, retained))
  have htarget :
      (split.symm (eval.symm g, retained)) target =
      (eval.symm g) ⟨target, rfl⟩ := by
    simpa only [periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_fst_apply] using hs
  have heval : (eval.symm g) ⟨target, rfl⟩ = g := by
    calc
      (eval.symm g) ⟨target, rfl⟩ = eval (eval.symm g) := by
        symm
        exact periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv_apply
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target (eval.symm g)
      _ = g := eval.apply_symm_apply g
  exact htarget.trans heval

/-- AX's original physical product-integrated conditional energy is
controlled by the PREEXISTING canonical weighted fiber variance functional.

The proof uses only (i) literal coordinate reconstruction, (ii) the fixed
Markov kernel's outer-a.e. agreement with the original normalized physical
fiber, (iii) pushforward invariance of variance, and (iv) Tonelli inequality.
No fiber mass is cancelled or divided out. -/
theorem p4Q2AY_originalIntegratedEnergy_le_canonicalFiberVariance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy
        H N hN beta hbeta target X ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target
        (p4Q2AY_originalOneLinkJointProbe H N target X) := by
  classical
  let muLeft := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let kappa :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  let nu := fun ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
      H N hN beta hbeta ctx.1 target ctx.2
  let mass := periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    H N hN beta hbeta target
  let F := p4Q2AY_originalOneLinkJointProbe H N target X
  have hkernel :
      ∀ᵐ left ∂muLeft, ∀ᵐ retained ∂muOff,
        kappa (left, retained) = nu (left, retained) := by
    simpa [muLeft, muOff, kappa, nu] using
      (Measure.ae_ae_of_ae_prod
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
          H N hN beta hbeta target))
  have hsection (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
      (fun targetCfg =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained (eval targetCfg)) =
      (fun targetCfg => X (eval targetCfg)) := by
    funext targetCfg
    change X (((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
      (eval.symm (eval targetCfg), retained)) target) = X (eval targetCfg)
    rw [p4Q2AY_reconstruct_target H N target retained (eval targetCfg)]
  have hIterated :
      (∫⁻ left, ∫⁻ retained,
        mass (left, retained) *
          evariance (fun g => X g) (Measure.map eval (nu (left, retained)))
        ∂muOff ∂muLeft) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
    change (∫⁻ left, ∫⁻ retained,
      mass (left, retained) *
        evariance (fun g => X g) (Measure.map eval (nu (left, retained)))
      ∂muOff ∂muLeft) =
      (∫⁻ left, ∫⁻ retained,
        mass (left, retained) *
          evariance
            (fun targetCfg =>
              periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F left retained (eval targetCfg))
            (kappa (left, retained))
        ∂muOff ∂muLeft)
    apply lintegral_congr_ae
    filter_upwards [hkernel] with left hleft
    apply lintegral_congr_ae
    filter_upwards [hleft] with retained hκ
    rw [hκ, hsection left retained]
    exact congrArg (fun v : ENNReal => mass (left, retained) * v)
      (p4Q2AY_evariance_map_measurableEquiv
        (nu (left, retained)) eval (fun g => X g) X.continuous.measurable)
  have hTonelli :
      periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy
          H N hN beta hbeta target X ≤
        (∫⁻ left, ∫⁻ retained,
          mass (left, retained) *
            evariance (fun g => X g) (Measure.map eval (nu (left, retained)))
          ∂muOff ∂muLeft) := by
    change (∫⁻ ctx,
      mass ctx * evariance (fun g => X g) (Measure.map eval (nu ctx))
      ∂muLeft.prod muOff) ≤
      (∫⁻ left, ∫⁻ retained,
        mass (left, retained) *
          evariance (fun g => X g) (Measure.map eval (nu (left, retained)))
        ∂muOff ∂muLeft)
    exact lintegral_prod_le
      (μ := muLeft) (ν := muOff)
      (fun ctx => mass ctx * evariance (fun g => X g) (Measure.map eval (nu ctx)))
  exact hTonelli.trans_eq hIterated

/-- AY: the ACTUAL AX Wilson lower bound is a genuine physical-Hilbert
conditional-expectation projection-residual lower bound on bounded continuous
one-link cylindrical observables. It is a local Dirichlet statement only. -/
theorem p4Q2AY_originalHaarReferenceEnergy_le_physicalCondExpResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedHaarReferenceEnergy
        H N hN beta hbeta target X ≤
      ENNReal.ofReal
        (‖p4Q2AY_originalOneLinkJointL2 H N hN beta hbeta target X -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (p4Q2AY_originalOneLinkJointL2 H N hN beta hbeta target X)‖ ^ 2) := by
  calc
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedHaarReferenceEnergy
        H N hN beta hbeta target X ≤
      periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy
        H N hN beta hbeta target X :=
      periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy_ge_Haar
        H N hN beta hbeta target X
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target (p4Q2AY_originalOneLinkJointProbe H N target X) :=
      p4Q2AY_originalIntegratedEnergy_le_canonicalFiberVariance
        H N hN beta hbeta target X
    _ = ENNReal.ofReal
        (‖p4Q2AY_originalOneLinkJointL2 H N hN beta hbeta target X -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (p4Q2AY_originalOneLinkJointL2 H N hN beta hbeta target X)‖ ^ 2) := by
      simpa only [p4Q2AY_originalOneLinkJointL2] using
        (GroundStateCanonicalMean.canonicalVariance_eq_condExpResidualNormSq
          H N hN beta hbeta target
          (p4Q2AY_originalOneLinkJointProbe H N target X)
          (p4Q2AY_originalOneLinkJointProbe_stronglyMeasurable H N target X)
          ‖X‖ (p4Q2AY_originalOneLinkJointProbe_norm_le H N target X))

end
end MathlibAnalytic
end MGAP4D
