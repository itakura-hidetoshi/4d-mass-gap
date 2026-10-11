import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAELinkHaarFiberZero
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# P4-Q2-CH: actual original Haar-link zero variance gives a.e. fiber constancy

CG proved that on every actual original right/left Wilson one-link Haar
section, zero original mass-weighted reference energy makes the genuine
SU(N) Haar variance vanish for outer-Haar-almost every context.

By the pinned mathlib theorem `evariance_eq_zero_iff`, those original
bounded concrete observables are now shown Haar-almost-everywhere equal
to THEIR OWN original Haar mean on each such link context. A second
consequence gives pairwise a.e. invariance when two independently
sampled target-link coordinates are substituted at the same context.

The results are on the EXACT physical Wilson original joint bounded
observable core and its actual Riesz-kernel image. No exceptional-context
pointwise assertion, arbitrary general-L² representative evaluation,
reverse Haar-Poincare inequality or full kernel equality is claimed.
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

/-- From zero extended Haar variance to actual fiber-wise a.e. constancy
at the genuine fiber Haar mean, with no L² quotient representative choice. -/
private theorem p4Q2CH_zero_evariance_ae_constant
    {G : Type*} [MeasurableSpace G] (mu : Measure G)
    (X : G → ℝ) (hX : AEStronglyMeasurable X mu)
    (hzero : evariance X mu = 0) :
    X =ᵐ[mu] (fun _ => mu[X]) :=
  (evariance_eq_zero_iff hX.aemeasurable).mp hzero

/-- Once a real Haar fiber has zero extended variance, two target-link
coordinates drawn from that same Haar law give the same observable value
almost everywhere in both coordinate slots. -/
private theorem p4Q2CH_zero_evariance_ae_pairwise
    {G : Type*} [MeasurableSpace G] (mu : Measure G)
    (X : G → ℝ) (hX : AEStronglyMeasurable X mu)
    (hzero : evariance X mu = 0) :
    ∀ᵐ g₁ ∂mu, ∀ᵐ g₂ ∂mu, X g₁ = X g₂ := by
  have hc : X =ᵐ[mu] (fun _ => mu[X]) :=
    p4Q2CH_zero_evariance_ae_constant mu X hX hzero
  filter_upwards [hc] with g₁ hg₁
  filter_upwards [hc] with g₂ hg₂
  exact hg₁.trans hg₂.symm

private abbrev p4Q2CH_ctx (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

private noncomputable def p4Q2CH_muOuter (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2CH_ctx H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

private noncomputable def p4Q2CH_section (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (ctx : p4Q2CH_ctx H N target) :
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
local notation "Ctx" => p4Q2CH_ctx H N
local notation "μOuter" => p4Q2CH_muOuter H N
local notation "μLink" => normalizedCompactHaar G
local notation "Section" => p4Q2CH_section H N

/-- Original right Wilson spatial link: zero actual mass-weighted Haar
reference gives a.e. constancy at its real direct Haar fiber mean. -/
theorem p4Q2CH_originalRightLinkHaarReferenceZero_implies_aeConstant
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    ∀ᵐ ctx ∂(μOuter target),
      Section target F ctx =ᵐ[μLink]
        (fun _ => μLink[Section target F ctx]) := by
  have hvar :=
    p4Q2CG_originalRightLinkHaarReferenceZero_implies_aeVarianceZero
      H N hN beta hbeta target F hF hzero
  filter_upwards [hvar] with ctx hv
  have hX : AEStronglyMeasurable (Section target F ctx) μLink :=
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
      H N target F hF ctx.1 ctx.2).aestronglyMeasurable (μ := μLink)
  exact p4Q2CH_zero_evariance_ae_constant μLink (Section target F ctx) hX hv

/-- Original right-link reference zero yields pairwise link-coordinate
invariance on two independent Haar coordinates, outer-almost-everywhere. -/
theorem p4Q2CH_originalRightLinkHaarReferenceZero_implies_pairwiseAE
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    ∀ᵐ ctx ∂(μOuter target),
      ∀ᵐ g₁ ∂μLink, ∀ᵐ g₂ ∂μLink,
        Section target F ctx g₁ = Section target F ctx g₂ := by
  have hvar :=
    p4Q2CG_originalRightLinkHaarReferenceZero_implies_aeVarianceZero
      H N hN beta hbeta target F hF hzero
  filter_upwards [hvar] with ctx hv
  have hX : AEStronglyMeasurable (Section target F ctx) μLink :=
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
      H N target F hF ctx.1 ctx.2).aestronglyMeasurable (μ := μLink)
  exact p4Q2CH_zero_evariance_ae_pairwise μLink (Section target F ctx) hX hv

/-- Endpoint swap gives the identical a.e.-constancy theorem for the
original physical LEFT spatial link without changing the Wilson law. -/
theorem p4Q2CH_originalLeftLinkHaarReferenceZero_implies_aeConstant
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (hzero : p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H N hN beta hbeta target F = 0) :
    ∀ᵐ ctx ∂(μOuter target),
      Section target (p4Q2BB_swapConcrete H N F) ctx =ᵐ[μLink]
        (fun _ => μLink[Section target (p4Q2BB_swapConcrete H N F) ctx]) := by
  exact p4Q2CH_originalRightLinkHaarReferenceZero_implies_aeConstant
    H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF) hzero

/-- On the LITERAL original Wilson bounded concrete physical joint core,
zero total Haar reference means all physical right and left spatial link
sections are Haar-a.e. constant at their OWN Haar mean, outer-a.e. -/
theorem p4Q2CH_originalCoreZero_implies_allLink_aeConstant
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        Section e.1 F.1 ctx =ᵐ[μLink]
          (fun _ => μLink[Section e.1 F.1 ctx])) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        Section e.1 (p4Q2BB_swapConcrete H N F.1) ctx =ᵐ[μLink]
          (fun _ => μLink[Section e.1 (p4Q2BB_swapConcrete H N F.1) ctx])) := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hlinks := (p4Q2CF_originalCoreZero_iff_all_links
    H N hN beta hbeta F).mp hzero
  constructor
  · intro color e
    exact p4Q2CH_originalRightLinkHaarReferenceZero_implies_aeConstant
      H N hN beta hbeta e.1 F.1 hF (hlinks.1 color e)
  · intro color e
    exact p4Q2CH_originalLeftLinkHaarReferenceZero_implies_aeConstant
      H N hN beta hbeta e.1 F.1 hF (hlinks.2 color e)

/-- For bounded-core images annihilated by the genuine original Wilson
Haar Riesz operator, the chosen concrete representative has exact
a.e. constant Haar sections in both physical boundaries. -/
theorem p4Q2CH_originalRieszCoreKernel_implies_allLink_aeConstant
    (x : Img) (hx : W (x : J) = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        Section e.1
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 ctx
          =ᵐ[μLink]
          (fun _ => μLink[Section e.1
            (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 ctx])) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      ∀ᵐ ctx ∂(μOuter e.1),
        Section e.1 (p4Q2BB_swapConcrete H N
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1) ctx
          =ᵐ[μLink]
          (fun _ => μLink[Section e.1 (p4Q2BB_swapConcrete H N
            (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1) ctx])) := by
  let F : Core := p4Q2BV_originalCoreRepresentative H N hN beta hbeta x
  have hQ : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0 := by
    have h :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta (x : J)).2 hx
    rw [p4Q2BX_originalFullJointQuadratic_on_range] at h
    exact h
  exact p4Q2CH_originalCoreZero_implies_allLink_aeConstant
    H N hN beta hbeta F hQ

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
