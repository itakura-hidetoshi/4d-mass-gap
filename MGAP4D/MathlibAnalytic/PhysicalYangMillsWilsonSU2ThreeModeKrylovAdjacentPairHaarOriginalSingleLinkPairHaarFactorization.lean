import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalHaarFiberMeanProductAE
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitContextCoordinateEquiv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-CJ: original Wilson Haar zero-fiber energy descends to true pair-Haar joint coordinates

CI proves actual original Wilson right/left one-link zero Haar-reference energy
implies that the observable equals its measurable Haar mean a.e. on the genuine
outer-Haar × target-SU(N)-Haar PRODUCT. The product law there is not an auxiliary
physical measure: a pinned, previously proven measurable equivalence identifies
it exactly with the ORIGINAL pair-Haar left × right configuration carrier.

We prove the direct singleton-target/evaluation measurable equivalence actually
PRESERVES the Haar measure (with the same original off-target coordinates) and
transport a.e. equality BACK to the full physical joint pair-Haar law. Thus a
zero-reference observable is pair-Haar-a.e. determined by the retained left
boundary and the off-target right spatial links, for EACH actual right link.
The same result is available for the original endpoint-swapped left links.

This is the missing single-coordinate factorization step before gluing finitely
many coordinate deletions into global constancy. No fake commutativity, new law,
reverse Poincare inequality, full Riesz kernel equality or 4d mass gap is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000
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

/-- A mean-factorization on the genuine outer × Haar-target product yields
a.e. strong measurability in precisely the retained-coordinate σ-algebra. -/
private theorem p4Q2CJ_product_ae_mean_implies_retained
    {Ctx G : Type*} [MeasurableSpace Ctx] [MeasurableSpace G]
    (μ : Measure Ctx) (ν : Measure G) [SFinite ν]
    (X : Ctx × G → ℝ) (hX : StronglyMeasurable X)
    (hAE : X =ᵐ[μ.prod ν] (fun z => ∫ t, X (z.1, t) ∂ν)) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace Ctx)] X (μ.prod ν) := by
  have hmean : Measurable (fun c : Ctx => ∫ t, X (c, t) ∂ν) :=
    hX.integral_prod_right'.measurable
  have hLift :
      Measurable[
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace Ctx)]
        (fun z : Ctx × G => ∫ t, X (z.1, t) ∂ν) := by
    exact hmean.comp (comap_measurable Prod.fst)
  exact hLift.stronglyMeasurable.aestronglyMeasurable.congr hAE.symm

/-- A measurable predicate transports BACK from a product along a genuine
measure-preserving measurable equivalence. -/
private theorem p4Q2CJ_ae_eq_of_measurePreserving_equiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B)
    (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν)
    (f g : B → ℝ) (hf : Measurable f) (hg : Measurable g)
    (h : (fun a => f (e a)) =ᵐ[μ] (fun a => g (e a))) :
    f =ᵐ[ν] g := by
  rw [← he.map_eq]
  exact (ae_map_iff e.measurable.aemeasurable
    (measurableSet_eq_fun hf hg)).2 h

private abbrev p4Q2CJ_ctx (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

private noncomputable def p4Q2CJ_outerHaar (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2CJ_ctx H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Ctx" => p4Q2CJ_ctx H N
local notation "muOuter" => p4Q2CJ_outerHaar H N
local notation "muLink" => normalizedCompactHaar G
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "Img" =>
  LinearMap.range (p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta)
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta

/-- The physical split-context link coordinate rebuilt from a direct
SU(N) Haar group variable is a genuine measurable equivalence to the
ORIGINAL left × right spatial configuration. -/
noncomputable def p4Q2CJ_directLinkJointMeasurableEquiv
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (Ctx target × G) ≃ᵐ Joint := by
  let ev := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := G) target
  exact ((MeasurableEquiv.refl (Ctx target)).prodCongr ev.symm).trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target)

/-- This actual direct-link coordinate equivalence takes outer × target
Haar EXACTLY to original physical pair Haar. There is no substitute law. -/
theorem p4Q2CJ_directLinkJoint_measPreserving
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurePreserving
      (p4Q2CJ_directLinkJointMeasurableEquiv H N target)
      ((muOuter target).prod muLink) muPair := by
  classical
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar G)
  let ev := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := G) target
  have hev : MeasurePreserving ev μTarget muLink := by
    have hFun :
        (ev : (PeriodicHypercubicEvenSpatialSliceTargetLink H target → G) → G) =
          Function.eval (⟨target, rfl⟩ :
            PeriodicHypercubicEvenSpatialSliceTargetLink H target) := by
      funext x
      simp [ev]
    rw [hFun]
    simpa [μTarget] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target => muLink)
        (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
  letI : SFinite (muOuter target) := by
    dsimp [p4Q2CJ_outerHaar]
    infer_instance
  have hLeft : MeasurePreserving
      ((MeasurableEquiv.refl (Ctx target)).prodCongr ev.symm)
      ((muOuter target).prod muLink) ((muOuter target).prod μTarget) := by
    simpa using (MeasurePreserving.id (muOuter target)).prod hev.symm
  have hRight : MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
        H N target)
      ((muOuter target).prod μTarget) muPair := by
    simpa [p4Q2CJ_outerHaar, μTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H N target)
  exact hLeft.trans hRight

/-- The literal Haar mean of a genuine full joint observable in the
selected RIGHT spatial link, defined on the ORIGINAL joint configuration
carrier and only depending on left boundary + retained off-target right. -/
noncomputable def p4Q2CJ_rightRetainedHaarMean
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) : Joint → ℝ :=
  fun z => ∫ t : G,
    Section target F z.1
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2) t ∂muLink

/-- The actual retained-coordinate Haar mean is measurable on the entire
original left/right pair-Haar configuration space. -/
theorem p4Q2CJ_rightRetainedHaarMean_measurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    Measurable (p4Q2CJ_rightRetainedHaarMean H N target F) := by
  have hsection :
      StronglyMeasurable (fun z : Ctx target × G =>
        Section target F z.1.1 z.1.2 z.2) := by
    have h := p4Q2CI_originalRightLinkSection_jointStronglyMeasurable
      H N target F hF
    change StronglyMeasurable (fun z : Ctx target × G =>
      Section target F z.1.1 z.1.2 z.2) at h
    exact h
  have hmean : Measurable (fun ctx : Ctx target =>
      ∫ t : G, Section target F ctx.1 ctx.2 t ∂muLink) :=
    hsection.integral_prod_right'.measurable
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := G) target
  have hOff : Measurable (fun x : Cfg =>
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target x) := by
    simpa only [periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd]
      using (measurable_snd.comp split.measurable)
  have hCtx : Measurable (fun z : Joint =>
      (z.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)) :=
    measurable_fst.prodMk (hOff.comp measurable_snd)
  exact hmean.comp hCtx

/-- The original Wilson mass-weighted RIGHT link with zero Haar reference
is now globally a.e. a function of its true retained physical joint
coordinates, on the ORIGINAL pair-Haar law (not only the split product). -/
theorem p4Q2CJ_originalRightLinkZero_pairHaarRetained
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    F =ᵐ[muPair] p4Q2CJ_rightRetainedHaarMean H N target F := by
  let e := p4Q2CJ_directLinkJointMeasurableEquiv H N target
  have he : MeasurePreserving e ((muOuter target).prod muLink) muPair :=
    p4Q2CJ_directLinkJoint_measPreserving H N target
  have hsource := p4Q2CI_originalRightLinkZero_implies_productAEFiberMean
    H N hN beta hbeta target F hF hzero
  change (fun z : Ctx target × G =>
      Section target F z.1.1 z.1.2 z.2) =ᵐ[(muOuter target).prod muLink]
    (fun z => ∫ t : G, Section target F z.1.1 z.1.2 t ∂muLink) at hsource
  have hcomp :
      (fun z : Ctx target × G => F (e z)) =ᵐ[(muOuter target).prod muLink]
        (fun z : Ctx target × G =>
          p4Q2CJ_rightRetainedHaarMean H N target F (e z)) := by
    have hleft (z : Ctx target × G) :
        F (e z) = Section target F z.1.1 z.1.2 z.2 := by
      rfl
    have hright (z : Ctx target × G) :
        p4Q2CJ_rightRetainedHaarMean H N target F (e z) =
          ∫ t : G, Section target F z.1.1 z.1.2 t ∂muLink := by
      let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
        (Gauge := G) target
      let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
        (Gauge := G) target
      have hOff :
          periodicHypercubicEvenSpatialSliceOffTargetRestriction target
            (split.symm (eval.symm z.2, z.1.2)) = z.1.2 := by
        rw [← periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd]
        exact congrArg Prod.snd (split.apply_symm_apply _)
      change (∫ t : G,
        Section target F z.1.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target
            (split.symm (eval.symm z.2, z.1.2))) t ∂muLink) =
            ∫ t : G, Section target F z.1.1 z.1.2 t ∂muLink
      rw [hOff]
    filter_upwards [hsource] with z hz
    calc
      F (e z) = Section target F z.1.1 z.1.2 z.2 := hleft z
      _ = ∫ t : G, Section target F z.1.1 z.1.2 t ∂muLink := hz
      _ = p4Q2CJ_rightRetainedHaarMean H N target F (e z) := (hright z).symm
  exact p4Q2CJ_ae_eq_of_measurePreserving_equiv
    ((muOuter target).prod muLink) muPair e he
    F (p4Q2CJ_rightRetainedHaarMean H N target F)
    hF.measurable
    (p4Q2CJ_rightRetainedHaarMean_measurable H N target F hF) hcomp

/-- The same pair-Haar coordinate factorization applies to the original
physical LEFT Wilson endpoint after its already proved endpoint swap. -/
theorem p4Q2CJ_originalLeftLinkZero_pairHaarSwappedRetained
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    p4Q2BB_swapConcrete H N F =ᵐ[muPair]
      p4Q2CJ_rightRetainedHaarMean H N target (p4Q2BB_swapConcrete H N F) := by
  exact p4Q2CJ_originalRightLinkZero_pairHaarRetained
    H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF) hzero

/-- Vanishing total literal original Wilson Haar reference forces
simultaneous true pair-Haar retained-coordinate factorization for every
right spatial link and every reflected-left spatial link. -/
theorem p4Q2CJ_originalCoreZero_pairHaar_all_links_retained
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    (∀ (color : Fin 6) (v : p4Q2BA_ColorLinks H color),
      (F.1 : Joint → ℝ) =ᵐ[muPair]
        p4Q2CJ_rightRetainedHaarMean H N v.1 F.1) ∧
    (∀ (color : Fin 6) (v : p4Q2BA_ColorLinks H color),
      p4Q2BB_swapConcrete H N F.1 =ᵐ[muPair]
        p4Q2CJ_rightRetainedHaarMean H N v.1
          (p4Q2BB_swapConcrete H N F.1)) := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hlinks := (p4Q2CF_originalCoreZero_iff_all_links
    H N hN beta hbeta F).mp hzero
  constructor
  · intro color v
    exact p4Q2CJ_originalRightLinkZero_pairHaarRetained
      H N hN beta hbeta v.1 F.1 hF (hlinks.1 color v)
  · intro color v
    exact p4Q2CJ_originalLeftLinkZero_pairHaarSwappedRetained
      H N hN beta hbeta v.1 F.1 hF (hlinks.2 color v)

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
