import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalZeroReferenceAllLinkDescent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitProductFiberMass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# P4-Q2-CG: actual original Wilson zero reference forces Haar-fiber variance zero a.e.

CF proved that zero LITERAL original Wilson twelve-color Haar reference on the
bounded real physical ground-state joint core is equivalent to vanishing of
every actual left/right original link mass-weighted reference integral.
The actual positive coefficient exp(-32*beta), the ORIGINAL ground-state
fiber-mass function (positive and finite outer-a.e. by the existing exact
split-product fiber-mass theorem), and the exact Haar fiber sections are
retained here, without a surrogate measure.

The proof establishes joint measurability of the concrete Haar sections and
measurability of their context-dependent Haar evariance from pinned mathlib's
Bochner-Fubini and Tonelli measurability theorems. A generic weighted-zero
lintegral lemma then removes the genuinely positive physical mass and the
strictly positive local coefficient. This yields a.e. ZERO Haar variance on
every original physical right/left link, for bounded concrete observables
of zero original reference energy, including bounded-core vectors in the
original Riesz operator kernel.

No pointwise claim at exceptional contexts, no assertion on arbitrary
pointwise representatives of general L² quotient vectors, no reverse
Poincare comparison, uniform spectral gap, or continuum mass gap is made.
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

/-- For a nonnegative measurable reference, zero of its integral against
a strictly positive a.e. mass and a strictly positive scalar forces the
UNWEIGHTED reference to vanish almost everywhere. The mass is only
a.e.-measurable: this matches original physical Wilson split-fiber masses. -/
private theorem p4Q2CG_weighted_zero_lintegral_implies_ae_zero
    {Ctx : Type*} [MeasurableSpace Ctx]
    (mu : Measure Ctx)
    (mass reference : Ctx → ENNReal) (coef : ENNReal)
    (hmass : AEMeasurable mass mu)
    (href : Measurable reference)
    (hmasspos : ∀ᵐ ctx ∂mu, mass ctx ≠ 0)
    (hcoef : coef ≠ 0)
    (hzero : (∫⁻ ctx, mass ctx * (coef * reference ctx) ∂mu) = 0) :
    reference =ᵐ[mu] 0 := by
  have hmeas :
      AEMeasurable (fun ctx => mass ctx * (coef * reference ctx)) mu :=
    hmass.mul ((measurable_const.mul href).aemeasurable)
  have hz :
      (fun ctx => mass ctx * (coef * reference ctx)) =ᵐ[mu] 0 :=
    (lintegral_eq_zero_iff' hmeas).mp hzero
  filter_upwards [hz, hmasspos] with ctx hctx hmassctx
  have hcoefref : coef * reference ctx = 0 :=
    (mul_eq_zero.mp hctx).resolve_left hmassctx
  exact (mul_eq_zero.mp hcoefref).resolve_left hcoef

/-- Measurability, in an arbitrary outer context, of the genuine Haar
variance of jointly strongly measurable real fiber sections. -/
private theorem p4Q2CG_evariance_section_measurable
    {Ctx G : Type*}
    [MeasurableSpace Ctx] [MeasurableSpace G]
    (muLink : Measure G) [SFinite muLink]
    (X : Ctx × G → ℝ) (hX : StronglyMeasurable X) :
    Measurable (fun ctx : Ctx => evariance (fun g => X (ctx, g)) muLink) := by
  have hmean :
      StronglyMeasurable (fun ctx : Ctx => ∫ g, X (ctx, g) ∂muLink) :=
    hX.integral_prod_right'
  have hcenter :
      Measurable (fun z : Ctx × G =>
        X z - ∫ g, X (z.1, g) ∂muLink) :=
    hX.measurable.sub (hmean.measurable.comp measurable_fst)
  have hsq : Measurable (fun z : Ctx × G =>
      ‖X z - ∫ g, X (z.1, g) ∂muLink‖ₑ ^ 2) :=
    hcenter.enorm.pow_const 2
  simpa only [evariance] using hsq.lintegral_prod_right'

/-- Actual outer left/off-target product carrier for one genuine Wilson spatial link. -/
private abbrev p4Q2CG_ctx (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Actual Haar product measure on the physical link's outer context. -/
private noncomputable def p4Q2CG_muOuter (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2CG_ctx H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- The literal original direct target SU(N) concrete fiber section. -/
private noncomputable def p4Q2CG_section (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (ctx : p4Q2CG_ctx H N target) :
    Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
    H N target F ctx.1 ctx.2

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
local notation "Off" => PeriodicHypercubicEvenSpatialSliceOffTargetLink H
local notation "Ctx" => p4Q2CG_ctx H N
local notation "μOuter" => p4Q2CG_muOuter H N
local notation "μLink" => normalizedCompactHaar G
local notation "Section" => p4Q2CG_section H N
local notation "Mass" =>
  periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    H N hN beta hbeta

/-- The ACTUAL physical joint bounded observable induces a jointly strongly
measurable Haar one-link section over outer left/off-target context and the
right direct SU(N) target coordinate. -/
private theorem p4Q2CG_originalHaarSection_jointStronglyMeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun z : Ctx target × G => Section target F z.1 z.2) := by
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

/-- The TRUE direct-Haar fiber variance is measurable as a function of all
original physical left and retained right off-target coordinates. -/
theorem p4Q2CG_originalHaarSection_evariance_measurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    Measurable (fun ctx : Ctx target => evariance (Section target F ctx) μLink) := by
  letI : IsProbabilityMeasure μLink := by
    infer_instance
  exact p4Q2CG_evariance_section_measurable μLink
    (fun z : Ctx target × G => Section target F z.1 z.2)
    (p4Q2CG_originalHaarSection_jointStronglyMeasurable
      H N target F hF)

/-- The ORIGINAL Wilson positive finite physical outer fiber mass is
a.e.-measurable with respect to exactly the original outer pair-Haar law.
This follows from the already certified split-density measurability and
mathlib's a.e.-Tonelli theorem; no fresh regularity hypothesis. -/
private theorem p4Q2CG_originalOuterMass_aemeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    AEMeasurable (Mass target) (μOuter target) := by
  let muTarget : Measure
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target → G) :=
    Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar G)
  have hw :
      AEMeasurable
        (fun z : Ctx target ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target → G) =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta z.1.1 target (z.2, z.1.2))
        ((μOuter target).prod muTarget) := by
    simpa [muTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
        H N hN beta hbeta target)
  simpa [periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass,
    muTarget] using hw.lintegral_prod_right'

/-- The ORIGINAL mass-weighted target Haar reference integral is zero only
when the literal target-section Haar variance is zero outer-a.e.
The positive mass is the ACTUAL Wilson split-target fiber mass and the
strictly positive scalar remains exp(-32 * beta). -/
theorem p4Q2CG_originalRightLinkHaarReferenceZero_implies_aeVarianceZero
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta target F = 0) :
    ∀ᵐ ctx ∂(μOuter target),
      evariance (Section target F ctx) μLink = 0 := by
  let mass : Ctx target → ENNReal := Mass target
  let reference : Ctx target → ENNReal :=
    fun ctx => evariance (Section target F ctx) μLink
  let coef : ENNReal := ENNReal.ofReal (Real.exp (-32 * beta))
  have hmassmeas : AEMeasurable mass (μOuter target) :=
    p4Q2CG_originalOuterMass_aemeasurable H N hN beta hbeta target
  have href : Measurable reference :=
    p4Q2CG_originalHaarSection_evariance_measurable
      H N target F hF
  have hmasspos : ∀ᵐ ctx ∂(μOuter target), mass ctx ≠ 0 := by
    filter_upwards [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top_prod
        H N hN beta hbeta target] with ctx hctx
    exact hctx.1.ne'
  have hcoef : coef ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hzero' :
      (∫⁻ ctx, mass ctx * (coef * reference ctx) ∂(μOuter target)) = 0 := by
    simpa [mass, reference, coef, p4Q2AZ_originalJointHaarReferenceEnergy,
      p4Q2CG_muOuter, p4Q2CG_section] using hzero
  have h := p4Q2CG_weighted_zero_lintegral_implies_ae_zero
    (μOuter target) mass reference coef
    hmassmeas href hmasspos hcoef hzero'
  exact h

/-- The endpoint-swapped ORIGINAL Wilson left spatial link has the same
almost-everywhere zero Haar fiber variance conclusion. The left energy
uses the already certified original physical joint swap, not a new law. -/
theorem p4Q2CG_originalLeftLinkHaarReferenceZero_implies_aeVarianceZero
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H N hN beta hbeta target F = 0) :
    ∀ᵐ ctx ∂(μOuter target),
      evariance (Section target (p4Q2BB_swapConcrete H N F) ctx) μLink = 0 := by
  exact p4Q2CG_originalRightLinkHaarReferenceZero_implies_aeVarianceZero
    H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF) hzero

/-- On the ORIGINAL bounded strongly measurable physical Wilson joint
observables, zero twelve-color Haar reference yields Haar variance zero
outer-almost-everywhere on EVERY actual right and left spatial link. -/
theorem p4Q2CG_originalCoreZero_implies_allLink_aeZeroVariance
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        evariance (Section e.1 F.1 ctx) μLink = 0) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        evariance
          (Section e.1 (p4Q2BB_swapConcrete H N F.1) ctx) μLink = 0) := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hlinks :=
    (p4Q2CF_originalCoreZero_iff_all_links H N hN beta hbeta F).mp hzero
  constructor
  · intro color e
    exact p4Q2CG_originalRightLinkHaarReferenceZero_implies_aeVarianceZero
      H N hN beta hbeta e.1 F.1 hF (hlinks.1 color e)
  · intro color e
    exact p4Q2CG_originalLeftLinkHaarReferenceZero_implies_aeVarianceZero
      H N hN beta hbeta e.1 F.1 hF (hlinks.2 color e)

/-- All physical original Haar one-link sections of a bounded-core vector
annihilated by the ACTUAL Wilson Riesz endomorphism have zero Haar variance
outer-a.e. This is NOT a theorem about arbitrary representatives of all L²
classes, and does not identify the entire Riesz kernel with constants. -/
theorem p4Q2CG_originalRieszCoreKernel_implies_allLink_aeZeroVariance
    (x : Img) (hx : W (x : J) = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        evariance
          (Section e.1
            (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 ctx)
          μLink = 0) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        evariance
          (Section e.1
            (p4Q2BB_swapConcrete H N
              (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1) ctx)
          μLink = 0) := by
  let F : Core := p4Q2BV_originalCoreRepresentative H N hN beta hbeta x
  have hQ : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0 := by
    have h :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta (x : J)).2 hx
    rw [p4Q2BX_originalFullJointQuadratic_on_range] at h
    exact h
  exact p4Q2CG_originalCoreZero_implies_allLink_aeZeroVariance
    H N hN beta hbeta F hQ

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
