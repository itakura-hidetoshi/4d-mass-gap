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
    measurableSet_eq_fun hX.measurable (hmean.comp measurable_fst)
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

/-- A named representation of the ORIGINAL full physical right-link
concrete Haar section on its true left/off-target × target group carrier.
Using an explicit name keeps elaboration independent of the huge dependent
configuration type; this is definitional, not a change in the physical law. -/
private noncomputable def p4Q2CI_actualSplitSection
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) : Ctx target × G → ℝ :=
  fun z => Section target F z.1.1 z.1.2 z.2

/-- The actual Haar fiber mean, now a nameable function of the entire
outer × direct-link Haar configuration. -/
private noncomputable def p4Q2CI_actualSplitMean
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) : Ctx target × G → ℝ :=
  fun z => ∫ t : G, Section target F z.1.1 z.1.2 t ∂muLink

/-- Actual bounded ORIGINAL Wilson joint observables have jointly strongly
measurable genuine direct SU(N) Haar one-link sections. The coordinate map
is the proved spatial-slice measurable equivalence, not a surrogate. -/
theorem p4Q2CI_originalRightLinkSection_jointStronglyMeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable (p4Q2CI_actualSplitSection H N target F) := by
  change StronglyMeasurable
    (fun z : Ctx target × G => Section target F z.1.1 z.1.2 z.2)
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

/-- Original Wilson zero Haar reference: a single a.e. equality with its
MEASURABLE actual Haar mean on the full genuine outer × target Haar product.
This upgrades CH's nested a.e. statement with no new physical assumption. -/
theorem p4Q2CI_originalRightLinkZero_implies_productAEFiberMean
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    p4Q2CI_actualSplitSection H N target F =ᵐ[(muOuter target).prod muLink]
      p4Q2CI_actualSplitMean H N target F := by
  have hsec :
      ∀ᵐ ctx ∂(muOuter target), ∀ᵐ g ∂muLink,
        Section target F ctx.1 ctx.2 g =
          ∫ t : G, Section target F ctx.1 ctx.2 t ∂muLink := by
    exact p4Q2CH_originalRightLinkHaarReferenceZero_implies_aeConstant
      H N hN beta hbeta target F hF hzero
  exact p4Q2CI_section_mean_glue (muOuter target) muLink
    (p4Q2CI_actualSplitSection H N target F)
    (p4Q2CI_originalRightLinkSection_jointStronglyMeasurable H N target F hF)
    hsec

/-- The same exact original Wilson left endpoint, via its already verified
physical joint-swap symmetry (without choosing a second Wilson law). -/
theorem p4Q2CI_originalLeftLinkZero_implies_productAEFiberMean
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    p4Q2CI_actualSplitSection H N target (p4Q2BB_swapConcrete H N F) =ᵐ[
      (muOuter target).prod muLink]
      p4Q2CI_actualSplitMean H N target (p4Q2BB_swapConcrete H N F) := by
  exact p4Q2CI_originalRightLinkZero_implies_productAEFiberMean
    H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF) hzero

/-- Zero TOTAL literal original Wilson Haar reference: simultaneous
right/left link product-a.e. Haar mean reconstruction on the TRUE physical
bounded observable core, with no exceptional-fiber pointwise assertion. -/
theorem p4Q2CI_originalCoreZero_implies_allLink_productAEFiberMean
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      p4Q2CI_actualSplitSection H N e.1 F.1 =ᵐ[(muOuter e.1).prod muLink]
        p4Q2CI_actualSplitMean H N e.1 F.1) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      p4Q2CI_actualSplitSection H N e.1 (p4Q2BB_swapConcrete H N F.1) =ᵐ[
        (muOuter e.1).prod muLink]
        p4Q2CI_actualSplitMean H N e.1 (p4Q2BB_swapConcrete H N F.1)) := by
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

/-- The same original physical Riesz-kernel-to-product-a.e. link factorization
for the bounded physical L² core image. No arbitrary quotient representative
is evaluated pointwise. -/
theorem p4Q2CI_originalRieszCoreKernel_implies_allLink_productAEFiberMean
    (x : Img) (hx : W (x : J) = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      p4Q2CI_actualSplitSection H N e.1
        (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 =ᵐ[
          (muOuter e.1).prod muLink]
        p4Q2CI_actualSplitMean H N e.1
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      p4Q2CI_actualSplitSection H N e.1
        (p4Q2BB_swapConcrete H N
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1) =ᵐ[
          (muOuter e.1).prod muLink]
        p4Q2CI_actualSplitMean H N e.1
          (p4Q2BB_swapConcrete H N
            (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1)) := by
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
