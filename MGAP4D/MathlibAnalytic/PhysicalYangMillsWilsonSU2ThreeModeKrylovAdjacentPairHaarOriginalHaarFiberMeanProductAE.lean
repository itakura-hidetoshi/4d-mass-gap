import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAELinkHaarFiberConstancy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-CI: original Wilson Haar-link a.e. constancy glues to product-a.e. fiber mean

CH proves that for a zero ORIGINAL Wilson mass-weighted Haar reference,
each genuine physical right/left link section agrees with its own Haar mean
for outer-Haar-a.e. context and target-Haar-a.e. group element.

The actual Haar fiber mean is jointly measurable in the outer context,
because the original physical concrete section is jointly strongly measurable.
We invoke mathlib's MEASURABLE product a.e. equivalence to turn these nested
claims into SINGLE product-Haar-a.e. equalities on the exact physical left
boundary × right off-target × target group carrier, for every right and
endpoint-swapped left link. No arbitrary L² representative is selected.

This is an exact intermediate descent step, not yet full-field pair-Haar
constancy, Riesz kernel equality, reverse reference Poincare, or any
continuum Yang--Mills mass gap.
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

/-- Nontrivial measure-theoretic glue: a measurable real function on an
actual product that is a.e. equal on each section to its mean, for
outer-a.e. context, is equal to the MEASURABLE lift of that mean for
product-a.e. configuration. The measurability hypothesis allows the use
of mathlib's full `Measure.ae_prod_iff_ae_ae` rather than only its
one-way Tonelli consequence. -/
private theorem p4Q2CI_section_mean_glue
    {Ctx G : Type*} [MeasurableSpace Ctx] [MeasurableSpace G]
    (muOuter : Measure Ctx) (muLink : Measure G) [SFinite muLink]
    (X : Ctx × G → ℝ) (hX : StronglyMeasurable X)
    (hsections :
      ∀ᵐ ctx ∂muOuter, ∀ᵐ g ∂muLink,
        X (ctx, g) = ∫ t, X (ctx, t) ∂muLink) :
    X =ᵐ[muOuter.prod muLink]
      (fun z => ∫ t, X (z.1, t) ∂muLink) := by
  have hmean :
      Measurable (fun ctx : Ctx => ∫ t, X (ctx, t) ∂muLink) :=
    hX.integral_prod_right'.measurable
  have heq :
      MeasurableSet
        {z : Ctx × G | X z = ∫ t, X (z.1, t) ∂muLink} :=
    measurableSet_eq hX.measurable (hmean.comp measurable_fst)
  exact (Measure.ae_prod_iff_ae_ae heq).2 hsections

private abbrev p4Q2CI_ctx (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

private noncomputable def p4Q2CI_muOuter (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2CI_ctx H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Ctx" => p4Q2CI_ctx H N
local notation "muOuter" => p4Q2CI_muOuter H N
local notation "muLink" => normalizedCompactHaar G
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- Actual bounded ORIGINAL Wilson joint observables have jointly strongly
measurable genuine direct SU(N) Haar one-link sections. The coordinate map
is the proved source spatial-slice measurable equivalence, not a surrogate. -/
theorem p4Q2CI_originalRightLinkSection_jointStronglyMeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (fun z : Ctx target × G => Section target F z.1.1 z.1.2 z.2) := by
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := G) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := G) target
  have htarg : Measurable (fun z : Ctx target × G => eval.symm z.2) :=
    eval.symm.measurable.comp measurable_snd
  have hret : Measurable (fun z : Ctx target × G => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hpair : Measurable (fun z : Ctx target × G =>
      (eval.symm z.2, z.1.2)) :=
    htarg.prodMk hret
  have hright : Measurable (fun z : Ctx target × G =>
      split.symm (eval.symm z.2, z.1.2)) :=
    split.symm.measurable.comp hpair
  have hcoord : Measurable (fun z : Ctx target × G =>
      (z.1.1, split.symm (eval.symm z.2, z.1.2))) :=
    (measurable_fst.comp measurable_fst).prodMk hright
  simpa [periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
    split, eval] using hF.comp_measurable hcoord

/-- Zero actual ORIGINAL physical right-link Haar reference implies equality
to the MEASURABLE Haar fiber mean on the whole outer × direct link product,
for pair-Haar-almost every combined configuration. -/
theorem p4Q2CI_originalRightLinkZero_implies_productAEFiberMean
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    (fun z : Ctx target × G => Section target F z.1.1 z.1.2 z.2) =ᵐ[
      (muOuter target).prod muLink]
      (fun z => ∫ t : G, Section target F z.1.1 z.1.2 t ∂muLink) := by
  have hsec :=
    p4Q2CH_originalRightLinkHaarReferenceZero_implies_aeConstant
      H N hN beta hbeta target F hF hzero
  change ∀ᵐ ctx ∂(muOuter target), ∀ᵐ g ∂muLink,
    Section target F ctx.1 ctx.2 g =
      ∫ t : G, Section target F ctx.1 ctx.2 t ∂muLink at hsec
  exact p4Q2CI_section_mean_glue (muOuter target) muLink
    (fun z : Ctx target × G => Section target F z.1.1 z.1.2 z.2)
    (p4Q2CI_originalRightLinkSection_jointStronglyMeasurable H N target F hF)
    hsec

/-- The SAME original physical left endpoint (via certified Wilson endpoint
swap), with unchanged actual Wilson measure and the exact Haar fiber mean. -/
theorem p4Q2CI_originalLeftLinkZero_implies_productAEFiberMean
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    (fun z : Ctx target × G =>
      Section target (p4Q2BB_swapConcrete H N F) z.1.1 z.1.2 z.2) =ᵐ[
      (muOuter target).prod muLink]
      (fun z => ∫ t : G,
        Section target (p4Q2BB_swapConcrete H N F) z.1.1 z.1.2 t ∂muLink) := by
  exact p4Q2CI_originalRightLinkZero_implies_productAEFiberMean
    H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF) hzero

/-- Original physical bounded core: every real right/left link section
is identified with its outer-measurable Haar mean in the ACTUAL Haar product,
provided the literal original Wilson twelve-color Haar reference is zero. -/
theorem p4Q2CI_originalCoreZero_implies_allLink_productAEFiberMean
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      (fun z : Ctx e.1 × G => Section e.1 F.1 z.1.1 z.1.2 z.2) =ᵐ[
        (muOuter e.1).prod muLink]
        (fun z => ∫ t : G, Section e.1 F.1 z.1.1 z.1.2 t ∂muLink)) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      (fun z : Ctx e.1 × G =>
        Section e.1 (p4Q2BB_swapConcrete H N F.1) z.1.1 z.1.2 z.2) =ᵐ[
        (muOuter e.1).prod muLink]
        (fun z => ∫ t : G,
          Section e.1 (p4Q2BB_swapConcrete H N F.1) z.1.1 z.1.2 t ∂muLink)) := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hlinks := (p4Q2CF_originalCoreZero_iff_all_links
    H N hN beta hbeta F).mp hzero
  constructor
  · intro color e
    exact p4Q2CI_originalRightLinkZero_implies_productAEFiberMean
      H N hN beta hbeta e.1 F.1 hF (hlinks.1 color e)
  · intro color e
    exact p4Q2CI_originalLeftLinkZero_implies_productAEFiberMean
      H N hN beta hbeta e.1 F.1 hF (hlinks.2 color e)

/-- The CI product-a.e. Haar mean factorization applies to the original
physical Wilson Riesz kernel intersected with the bounded observable core. -/
theorem p4Q2CI_originalRieszCoreKernel_implies_allLink_productAEFiberMean
    (x : Img) (hx : W (x : J) = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      (fun z : Ctx e.1 × G => Section e.1
        (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1
        z.1.1 z.1.2 z.2) =ᵐ[(muOuter e.1).prod muLink]
        (fun z => ∫ t : G, Section e.1
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1
          z.1.1 z.1.2 t ∂muLink)) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      (fun z : Ctx e.1 × G => Section e.1
        (p4Q2BB_swapConcrete H N
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1)
        z.1.1 z.1.2 z.2) =ᵐ[(muOuter e.1).prod muLink]
        (fun z => ∫ t : G, Section e.1
          (p4Q2BB_swapConcrete H N
            (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1)
          z.1.1 z.1.2 t ∂muLink)) := by
  let F : Core := p4Q2BV_originalCoreRepresentative H N hN beta hbeta x
  have hQ : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0 := by
    have h := (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta (x : J)).2 hx
    rw [p4Q2BX_originalFullJointQuadratic_on_range] at h
    exact h
  exact p4Q2CI_originalCoreZero_implies_allLink_productAEFiberMean
    H N hN beta hbeta F hQ

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
