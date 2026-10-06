import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorMeasureBridge
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Posterior fiber identities under the genuine joint ground-state law

The previous bridge identifies normalized genuine and posterior fiber laws on
nested Haar-a.e. left/off-target contexts.  An arbitrary nested a.e. predicate
cannot be promoted to a product-a.e. statement by an unqualified converse of
Fubini.  Instead, this file lifts the two independent representative events:

* the global left-vacuum representative event through the left projection;
* the off-target fiber representative event through the canonical Haar split
  and then the right projection.

Their intersection gives pair-Haar-a.e. equality of the normalized fiber laws.
The literal withDensity definition of the genuine joint law then transfers
this equality by absolute continuity, without a comparison constant.

All bounded-continuous fiber tests agree on the same full-measure joint event.
This is a measure/representative bridge, not yet a joint-L2 conditional-
expectation operator identity or a stagewise oscillation-tail bound.  No
exceptional fixed fiber or posterior-sweep/Euclidean-time identity is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance posteriorJointAEBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorJointAEBridgeCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorJointAEBridgeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorJointAEBridgeMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorJointAEBridgeBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorJointAEBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorJointAEBridgeTargetLinkFintype
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

namespace GroundStatePosteriorFiberBridge

/-- Forgetting the target coordinate preserves null off-target events. -/
theorem offTargetRestriction_quasiMeasurePreserving
    (H N : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure.QuasiMeasurePreserving
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) := by
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
  have hsplit : MeasurePreserving split μ (μTarget.prod μOff) := by
    simpa [split, μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
        H N target)
  change Measure.QuasiMeasurePreserving (Prod.snd ∘ split) μ μOff
  exact (Measure.quasiMeasurePreserving_snd (μ := μTarget) (ν := μOff)).comp
    hsplit.quasiMeasurePreserving

private theorem normalizedMeasure_eq_of_ae_weights
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w w' : α → ℝ≥0∞) (h : w =ᵐ[μ] w') :
    doobWeightedMeasure μ w = doobWeightedMeasure μ w' := by
  have hMass : doobWeightMass μ w = doobWeightMass μ w' := by
    simpa [doobWeightMass] using lintegral_congr_ae h
  unfold doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  simp only [doobWeightedDensity]
  rw [hx, hMass]

/-- Two independent full-measure representative events identify the historical
fiber laws under pair Haar.  No converse-Fubini measurability premise is hidden. -/
theorem normalizedFiberMeasure_pairHaar_ae_eq_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta z.1 z.2 target =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta z.1 z.2 target := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μGroup := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let omega : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 A
  let omegaC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let topNorm :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖
  have hLeft : omegaC =ᵐ[μ] omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta
  have hOff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing_updateTarget_of_offTarget
      H N hN beta hbeta target
  have hRight :
      ∀ᵐ right ∂μ,
        (fun g => omegaC (Function.update right target g)) =ᵐ[μGroup]
          fun g => omega (Function.update right target g) := by
    have hContext := (offTargetRestriction_quasiMeasurePreserving H N target).ae hOff
    filter_upwards [hContext] with right hright
    exact hright right rfl
  have hLeftPair := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hLeft
  have hRightPair := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hRight
  change ∀ᵐ z ∂(μ.prod μ), _
  filter_upwards [hLeftPair, hRightPair] with z hzLeft hzRight
  have hWeight :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta z.1 z.2 target =ᵐ[μGroup]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
          H N hN beta hbeta z.1 z.2 target := by
    filter_upwards [hzRight] with g hg
    change
      ENNReal.ofReal
          (topNorm⁻¹ * (omega z.1 * K z.1 (Function.update z.2 target g) *
            omega (Function.update z.2 target g))) =
        ENNReal.ofReal
          (topNorm⁻¹ * (omegaC z.1 * K z.1 (Function.update z.2 target g) *
            omegaC (Function.update z.2 target g)))
    rw [← hzLeft, ← hg]
  exact (normalizedMeasure_eq_of_ae_weights μGroup _ _ hWeight).trans
    (continuousCompatible_eq_posterior H N hN beta hbeta z.1 z.2 target)

/-- The actual joint ground-state measure inherits the fiber-law identity
from pair Haar by the absolute continuity of its literal withDensity. -/
theorem normalizedFiberMeasure_joint_ae_eq_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta z.1 z.2 target =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta z.1 z.2 target := by
  have hAC :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta ≪
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N :=
    withDensity_absolutelyContinuous _ _
  exact (normalizedFiberMeasure_pairHaar_ae_eq_posterior
    H N hN beta hbeta target).filter_mono hAC.ae_le

/-- For joint-almost every boundary pair, all BCF fiber tests agree with the
posterior conditional expectation.  The exceptional set is test-independent. -/
theorem fiberIntegral_joint_ae_eq_posteriorConditionalExpectation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta,
      ∀ O : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ,
        (∫ g, O (Function.update z.2 target g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
            H N hN beta hbeta z.1 z.2 target) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta z.1 O z.2 target := by
  filter_upwards [normalizedFiberMeasure_joint_ae_eq_posterior
    H N hN beta hbeta target] with z hz
  intro O
  rw [hz]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
      H N hN beta hbeta z.1 O z.2 target).symm

end GroundStatePosteriorFiberBridge

end

end MGAP4D.MathlibAnalytic
