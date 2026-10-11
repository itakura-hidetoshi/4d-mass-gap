import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSingleLinkPairHaarFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarBoundaryAEMeasurability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStatePairHaarQualitativeBoundaryCollapse
import Mathlib.Tactic

/-!
# P4-Q2-CK: genuine all-link Wilson Haar descent and pair-Haar a.e. constancy

CJ has established literal one-target-link Haar-mean factorization on the
ORIGINAL left × right pair Haar law for zero Wilson reference. Here we
identify its precise retained-coordinate sigma algebra, intersect these
supports over ALL actual finite right links by the previously proved
finite-product Fubini coordinate-intersection lemma, and deduce dependence
only on the full left boundary. The actual left Wilson link statement
repeats the same argument after the proved endpoint swap. The two resulting
boundary factorizations imply almost-everywhere constancy.

All conclusions are for the ORIGINAL bounded strongly measurable Wilson
concrete core and its specifically chosen physical L² core representative.
They do not claim full physical L² kernel equality, reverse coercivity,
volume-uniform positive spectral gap or any continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2400000
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

/-- Finite many genuine coordinate restrictions can be intersected using
only the proved TWO-support product/Fubini intersection. An explicit anchor
avoids any hidden nonemptiness assumption on the finite index carrier. -/
private theorem p4Q2CK_allSupports
    {Ω ι K κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [MeasurableSpace K]
    (ω : Measure Ω) (η : Measure K) [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (ι → K))
    (he : MeasurePreserving e ω (Measure.pi (fun _ : ι => η)))
    (anchor : κ) (p : κ → ι → Prop) [∀ k, DecidablePred (p k)]
    (f : Ω → ℝ)
    (h : ∀ k : κ,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K) (p k)) ∘ e)
          (inferInstance : MeasurableSpace ({i : ι // p k i} → K))]
        f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) (fun i => ∀ k : κ, p k i)) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // ∀ k : κ, p k i} → K))]
      f ω := by
  classical
  have hfin : ∀ s : Finset κ,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K)
              (fun i => p anchor i ∧ ∀ k ∈ s, p k i)) ∘ e)
          (inferInstance : MeasurableSpace
            ({i : ι // p anchor i ∧ ∀ k ∈ s, p k i} → K))]
        f ω := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hp :
            (fun i : ι => p anchor i ∧ ∀ k ∈ (∅ : Finset κ), p k i) =
              p anchor := by
          funext i
          simp
        simpa only [hp] using h anchor
    | @insert k s hk hs =>
        have hAnd :=
          aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
            ω η e he
            (fun i : ι => p anchor i ∧ ∀ t ∈ s, p t i) (p k)
            f hs (h k)
        have hp :
            (fun i : ι => p anchor i ∧ ∀ t ∈ insert k s, p t i) =
              (fun i : ι => (p anchor i ∧ ∀ t ∈ s, p t i) ∧ p k i) := by
          funext i
          apply propext
          constructor
          · rintro ⟨ha, hall⟩
            refine ⟨⟨ha, ?_⟩, hall k (Finset.mem_insert_self k s)⟩
            intro t ht
            exact hall t (Finset.mem_insert_of_mem ht)
          · rintro ⟨⟨ha, hall⟩, hk'⟩
            refine ⟨ha, ?_⟩
            intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht'
            · exact hk'
            · exact hall t ht'
        simpa only [hp] using hAnd
  have hall := hfin Finset.univ
  have hp :
      (fun i : ι => p anchor i ∧ ∀ k ∈ (Finset.univ : Finset κ), p k i) =
        (fun i : ι => ∀ k : κ, p k i) := by
    funext i
    apply propext
    constructor
    · intro hh k
      exact hh.2 k (Finset.mem_univ k)
    · intro hh
      exact ⟨hh anchor, fun k _ => hh k⟩
  simpa only [hp] using hall

/-- Endpoint swap transfers a first-boundary a.e. measurable representation
into a second-boundary a.e. measurable representation on the SAME independent
pair probability law. -/
private theorem p4Q2CK_swap_fst_to_snd
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ]
    (f : X × X → ℝ)
    (h : AEStronglyMeasurable[
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace X)]
      (fun z : X × X => f z.swap) (μ.prod μ)) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace X)]
      f (μ.prod μ) := by
  have hmk := h.stronglyMeasurable_mk
  obtain ⟨L, hL, hLfac⟩ := hmk.exists_eq_measurable_comp
  have hsource :
      (fun z : X × X => f z.swap) =ᵐ[μ.prod μ]
        (fun z : X × X => L z.1) := by
    have hh := h.ae_eq_mk
    rw [hLfac] at hh
    simpa [Function.comp_def] using hh
  have hswap : MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap
  have hdest :
      f =ᵐ[μ.prod μ] (fun z : X × X => L z.2) := by
    have hh := hswap.quasiMeasurePreserving.ae_eq hsource
    simpa [Prod.swap, Function.comp_def] using hh
  have hsmall :
      Measurable[
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace X)]
        (fun z : X × X => L z.2) :=
    hL.comp (comap_measurable Prod.snd)
  exact hsmall.stronglyMeasurable.aestronglyMeasurable.congr hdest.symm

/-- A single right link's deletion retains every left coordinate and all
right coordinates other than that genuine target. -/
def p4Q2CK_rightSupport (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) : Prop :=
  match i with
  | Sum.inl _ => True
  | Sum.inr e => e ≠ target

/-- Literal retained link values recover left-boundary configuration and
off-target right-boundary configuration; no new configuration law is used. -/
def p4Q2CK_rightContextDecoder (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (({i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H //
         p4Q2CK_rightSupport H target i} →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun x =>
    (fun e => x ⟨Sum.inl e, trivial⟩,
     fun e => x ⟨Sum.inr e.1, e.2⟩)

theorem p4Q2CK_rightContextDecoder_measurable (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable (p4Q2CK_rightContextDecoder H N target) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply
      (⟨Sum.inl i, trivial⟩ :
        {i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H //
          p4Q2CK_rightSupport H target i})
  · rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply
      (⟨Sum.inr i.1, i.2⟩ :
        {i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H //
          p4Q2CK_rightSupport H target i})

/-- The previous decoder is exactly the original spatial configuration's
left boundary together with its genuine right off-target restriction. -/
theorem p4Q2CK_rightContext_eq (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (z.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)) =
      p4Q2CK_rightContextDecoder H N target ∘
        ((pairHaarPiRestriction (K := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (p4Q2CK_rightSupport H target)) ∘
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N) := by
  funext z
  apply Prod.ext
  · funext e
    rfl
  · funext e
    rfl

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" =>
  PeriodicHypercubicEvenSpatialSliceLink H
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "Img" =>
  LinearMap.range (p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta)
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta

/-- CJ's genuine pair-Haar target mean factors measurably through the
EXACT retained left+off-target-right finite coordinate restriction. -/
theorem p4Q2CK_rightRetainedHaarMean_smallMeasurable
    (target : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    Measurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := G) (p4Q2CK_rightSupport H target)) ∘
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H)
        (inferInstance : MeasurableSpace
          ({i : I // p4Q2CK_rightSupport H target i} → G))]
      (p4Q2CJ_rightRetainedHaarMean H N target F) := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N
  let r := (pairHaarPiRestriction (K := G) (p4Q2CK_rightSupport H target)) ∘ E
  have hsec : StronglyMeasurable
      (fun z : (Cfg ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G)) × G =>
        Section target F z.1.1 z.1.2 z.2) := by
    have hs := p4Q2CI_originalRightLinkSection_jointStronglyMeasurable
      H N target F hF
    change StronglyMeasurable
      (fun z : (Cfg ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G)) × G =>
        Section target F z.1.1 z.1.2 z.2) at hs
    exact hs
  have hmean : Measurable
      (fun ctx : Cfg ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G) =>
        ∫ t : G, Section target F ctx.1 ctx.2 t ∂normalizedCompactHaar G) :=
    hsec.integral_prod_right'.measurable
  have hctx : Measurable[MeasurableSpace.comap r inferInstance]
      (fun z : Joint =>
        (z.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)) := by
    rw [p4Q2CK_rightContext_eq H N target]
    exact (p4Q2CK_rightContextDecoder_measurable H N target).comp
      (comap_measurable r)
  have hsmall := hmean.comp hctx
  simpa only [p4Q2CJ_rightRetainedHaarMean, Function.comp_def] using hsmall

/-- Exact zero original right Wilson Haar-reference now gives pair-Haar
a.e. strong measurability with respect to deletion of that ONE genuine
spatial right link, rather than merely equality with a named mean. -/
theorem p4Q2CK_originalRightLinkZero_smallSigma
    (target : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := G) (p4Q2CK_rightSupport H target)) ∘
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N)
        (inferInstance : MeasurableSpace
          ({i : I // p4Q2CK_rightSupport H target i} → G))]
      F muPair := by
  have hmean :=
    p4Q2CK_rightRetainedHaarMean_smallMeasurable
      H N hN beta hbeta target F hF
  have hae :=
    p4Q2CJ_originalRightLinkZero_pairHaarRetained
      H N hN beta hbeta target F hF hzero
  exact hmean.stronglyMeasurable.aestronglyMeasurable.congr hae.symm

/-- If the LITERAL ORIGINAL right Wilson Haar-reference vanishes in EVERY
link, the joint function is pair-Haar-a.e. measurable using only its LEFT
boundary. This is finite-product descent, not an assumed independence of
Wilson link conditionals. -/
theorem p4Q2CK_originalRightAllLinkZero_leftBoundary
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : ∀ target : Link,
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta target F = 0) :
    AEStronglyMeasurable[
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Cfg)]
      F muPair := by
  classical
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N
  let η : Measure G := normalizedCompactHaar G
  have he : MeasurePreserving E muPair (Measure.pi (fun _ : I => η)) := by
    simpa [E, η] using
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
        H N)
  have hsingle : ∀ target : Link,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := G) (p4Q2CK_rightSupport H target)) ∘ E)
          (inferInstance : MeasurableSpace
            ({i : I // p4Q2CK_rightSupport H target i} → G))]
        F muPair := by
    intro target
    exact p4Q2CK_originalRightLinkZero_smallSigma
      H N hN beta hbeta target F hF (hzero target)
  have hall :=
    p4Q2CK_allSupports muPair η E he
      (p4Q2BA_sixColorRepresentatives H 0)
      (p4Q2CK_rightSupport H) F hsingle
  have hp :
      (fun i : I => ∀ target : Link, p4Q2CK_rightSupport H target i) =
        (fun i : I =>
          match i with
          | Sum.inl _ => True
          | Sum.inr _ => False) := by
    funext i
    cases i with
    | inl e =>
        simp [p4Q2CK_rightSupport]
    | inr e =>
        apply propext
        constructor
        · intro hh
          exact (hh e) rfl
        · intro hh
          exact False.elim hh
  rw [hp] at hall
  have hboundary :
      Measurable[
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Cfg)]
        ((pairHaarPiRestriction (K := G)
            (fun i : I =>
              match i with
              | Sum.inl _ => True
              | Sum.inr _ => False)) ∘ E) := by
    letI : MeasurableSpace Joint :=
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Cfg)
    change Measurable
      ((pairHaarPiRestriction (K := G)
        (fun i : I =>
          match i with
          | Sum.inl _ => True
          | Sum.inr _ => False)) ∘ E)
    rw [measurable_pi_iff]
    intro i
    rcases i with ⟨i, hi⟩
    cases i with
    | inl e =>
        change Measurable (fun z : Joint => z.1 e)
        exact (measurable_pi_apply e).comp
          (measurable_iff_comap_le.mpr le_rfl)
    | inr e =>
        change False at hi
        contradiction
  exact hall.mono (measurable_iff_comap_le.mp hboundary)

/-- First qualitative global theorem for the actual original Wilson
bounded physical core: vanishing literal reference implies an honest
pair-Haar-a.e. constant, via all physical RIGHT and LEFT links. -/
theorem p4Q2CK_originalCoreZero_pairHaar_aeConst
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    ∃ c : ℝ, (F.1 : Joint → ℝ) =ᵐ[muPair] (fun _ => c) := by
  classical
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hlink := (p4Q2CF_originalCoreZero_iff_all_links
    H N hN beta hbeta F).mp hzero
  have hright : ∀ target : Link,
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta target F.1 = 0 := by
    intro target
    let c := periodicHypercubicEvenGroundStateSpatialColorEquivFin
      (periodicHypercubicEvenSpatialSliceLinkColor H target)
    have hc :
        periodicHypercubicEvenSpatialSliceLinkColor H target =
          periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c := by
      simp [c]
    exact hlink.1 c ⟨target, hc⟩
  have hleft : ∀ target : Link,
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta target (p4Q2BB_swapConcrete H N F.1) = 0 := by
    intro target
    let c := periodicHypercubicEvenGroundStateSpatialColorEquivFin
      (periodicHypercubicEvenSpatialSliceLinkColor H target)
    have hc :
        periodicHypercubicEvenSpatialSliceLinkColor H target =
          periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c := by
      simp [c]
    exact hlink.2 c ⟨target, hc⟩
  have hfirst :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Cfg)]
        (F.1 : Joint → ℝ) muPair :=
    p4Q2CK_originalRightAllLinkZero_leftBoundary
      H N hN beta hbeta F.1 hF hright
  have hswapped :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Cfg)]
        (p4Q2BB_swapConcrete H N F.1) muPair :=
    p4Q2CK_originalRightAllLinkZero_leftBoundary
      H N hN beta hbeta
      (p4Q2BB_swapConcrete H N F.1)
      (p4Q2BB_swapConcrete_stronglyMeasurable H N F.1 hF)
      hleft
  have hsecond :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Cfg)]
        (F.1 : Joint → ℝ) muPair := by
    exact p4Q2CK_swap_fst_to_snd
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      F.1 hswapped
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_ae_eq_const_of_fst_snd_aestronglyMeasurable
      H N F.1 hfirst hsecond

/-- The proven original physical Wilson joint law has the same null sets
as pair Haar. Hence qualitative bounded-core constancy is also on the
ACTUAL positive-beta physical joint law. No L² norm comparison is used. -/
theorem p4Q2CK_originalCoreZero_physicalJoint_aeConst
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    ∃ c : ℝ,
      (F.1 : Joint → ℝ) =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta] (fun _ => c) := by
  obtain ⟨c, hc⟩ :=
    p4Q2CK_originalCoreZero_pairHaar_aeConst
      H N hN beta hbeta F hzero
  exact ⟨c, (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_ae_eq_iff_pairHaar
    H N hN beta hbeta F.1 (fun _ => c)).2 hc⟩

/-- On the concrete image of the ORIGINAL physical joint L² core, an
original Wilson Riesz-kernel vector is represented by a genuine
pair-Haar-a.e. constant observable. Full physical L² range extension is
still a separate, unproved theorem. -/
theorem p4Q2CK_originalRieszCoreKernel_pairHaar_aeConst
    (x : Img) (hx : W (x : J) = 0) :
    ∃ c : ℝ,
      ((p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 : Joint → ℝ)
        =ᵐ[muPair] (fun _ => c) := by
  let F : Core := p4Q2BV_originalCoreRepresentative H N hN beta hbeta x
  have hq :
      p4Q2BP_originalCoreReference H N hN beta hbeta F = 0 := by
    have h := (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta (x : J)).2 hx
    rw [p4Q2BX_originalFullJointQuadratic_on_range] at h
    exact h
  exact p4Q2CK_originalCoreZero_pairHaar_aeConst
    H N hN beta hbeta F hq

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
