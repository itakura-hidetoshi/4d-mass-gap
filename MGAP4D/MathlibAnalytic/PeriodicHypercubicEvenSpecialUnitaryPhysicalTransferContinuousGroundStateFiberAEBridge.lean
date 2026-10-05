import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatio
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectNormalizedFiberBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRepresentative
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# AE bridge from the continuous vacuum fiber to the genuine ground-state fiber

PR #5150 constructs an everywhere-defined continuous positive complete
one-link fiber weight.  The historical genuine ground-state joint density was
constructed earlier from an L2 representative of the physical vacuum.

Those representatives agree only almost everywhere.  Therefore the correct
bridge is not a pointwise equality for every retained context.

This file transports the established global Haar-a.e. equality through the
canonical target/off-target Haar split, applies Fubini, and obtains:

* for off-target-Haar-a.e. retained context, the continuous vacuum and the old
  L2 representative agree target-Haar-a.e. along the selected fiber;
* consequently, for Haar-a.e. left boundary and off-target-Haar-a.e. retained
  context, the historical genuine one-link fiber weight agrees target-Haar-a.e.
  with the continuous-compatible complete weight;
* normalized Doob-weighted fiber measures are therefore exactly equal on those
  a.e. contexts.

No exceptional fixed fiber is promoted to a pointwise theorem.  No RCD,
Euclidean-time identification, H1-D5 exact descent, or complete Yang--Mills
mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance continuousGroundStateFiberAEBridgeTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousGroundStateFiberAEBridgeCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousGroundStateFiberAEBridgeSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousGroundStateFiberAEBridgeMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousGroundStateFiberAEBridgeBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousGroundStateFiberAEBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance continuousGroundStateFiberAEBridgeTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance continuousGroundStateFiberAEBridgeTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

private theorem doobWeightedMeasure_eq_of_ae_eq_bridge
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w w' : α → ℝ≥0∞)
    (h : w =ᵐ[μ] w') :
    doobWeightedMeasure μ w = doobWeightedMeasure μ w' := by
  have hMass :
      doobWeightMass μ w = doobWeightMass μ w' := by
    simpa [doobWeightMass] using lintegral_congr_ae h
  unfold doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  simp only [doobWeightedDensity]
  rw [hx, hMass]

/-- The continuous vacuum and the historical L2 representative agree along
the selected singleton target factor for off-target-Haar-a.e. retained
context.

This is exactly the Fubini form of the global a.e. representative theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing_splitTargetFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
      ∀ᵐ targetCfg ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
              (targetCfg, retained)) =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1
            ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
              (targetCfg, retained)) := by
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
  have hsplitInv : MeasurePreserving split.symm (μTarget.prod μOff) μ :=
    hsplit.symm
  have hglobal :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta) =ᵐ[μ]
      fun B =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 B := by
    simpa [μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
        H N hN beta hbeta)
  have hsplitAE :
      ∀ᵐ z ∂(μTarget.prod μOff),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (split.symm z) =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 (split.symm z) :=
    hsplitInv.quasiMeasurePreserving.ae hglobal
  have hswap :
      ∀ᵐ z ∂(μOff.prod μTarget),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (split.symm z.swap) =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 (split.symm z.swap) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hsplitAE
  simpa [μTarget, μOff, split, Prod.swap] using
    (Measure.ae_ae_of_ae_prod hswap)

/-- For off-target-Haar-a.e. retained context, every complete right boundary
with that retained context has target-Haar-a.e. equality between the continuous
vacuum and the historical representative after target replacement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing_updateTarget_of_offTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
      ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = retained →
          (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta (Function.update right target g)) =ᵐ[
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)]
          fun g =>
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 (Function.update right target g) := by
  classical
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μGroup := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
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
  have hfiber :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing_splitTargetFiber
      H N hN beta hbeta target
  change ∀ᵐ retained ∂μOff, _
  filter_upwards [by simpa [μTarget, μOff, split] using hfiber] with retained hretained
  intro right hoff
  have htarget :
      ∀ᵐ g ∂μGroup,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (split.symm (eval.symm g, retained)) =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 (split.symm (eval.symm g, retained)) :=
    heval.symm.quasiMeasurePreserving.ae hretained
  filter_upwards [htarget] with g hg
  have hcoord :
      split.symm (eval.symm g, retained) = Function.update right target g := by
    have h :=
      periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update
        target right (eval.symm g)
    rw [hoff] at h
    simpa [split, eval] using h
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update right target g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (split.symm (eval.symm g, retained)) := by
          rw [hcoord]
    _ = (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 (split.symm (eval.symm g, retained)) := hg
    _ = (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 (Function.update right target g) := by
          rw [hcoord]

/-- Continuous-compatible ENNReal fiber weight retaining the exact historical
left-vacuum and transfer-norm scalar factors, but using the canonical
continuous vacuum representative pointwise. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta left *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left (Function.update right target g) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update right target g)))

/-- On the exact a.e. context set generated above, the historical genuine fiber
weight and the continuous-compatible complete fiber weight agree target-Haar
almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_ae_eq_continuousCompatible
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = retained →
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
                H N hN beta hbeta left right target =ᵐ[
                  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)]
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
                H N hN beta hbeta left right target := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have hleft :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta
  have hright :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing_updateTarget_of_offTarget
      H N hN beta hbeta target
  change ∀ᵐ left ∂μ, _
  filter_upwards [by simpa [μ] using hleft] with left hleftEq
  change ∀ᵐ retained ∂μOff, _
  filter_upwards [by simpa [μOff] using hright] with retained hretained
  intro right hoff
  filter_upwards [hretained right hoff] with g hrightEq
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
  rw [← hleftEq, ← hrightEq]

/-- Therefore the historical normalized genuine target-fiber measure equals
the normalized continuous-compatible fiber measure for the same a.e. set of
left/off-target contexts. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_ae_eq_continuousCompatible
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = retained →
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
                H N hN beta hbeta left right target =
              doobWeightedMeasure
                (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
                  H N hN beta hbeta left right target) := by
  have hWeight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_ae_eq_continuousCompatible
      H N hN beta hbeta target
  filter_upwards [hWeight] with left hleft
  filter_upwards [hleft] with retained hretained
  intro right hoff
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
  exact
    doobWeightedMeasure_eq_of_ae_eq_bridge
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
        H N hN beta hbeta left right target)
      (hretained right hoff)

end

end MathlibAnalytic
end MGAP4D
