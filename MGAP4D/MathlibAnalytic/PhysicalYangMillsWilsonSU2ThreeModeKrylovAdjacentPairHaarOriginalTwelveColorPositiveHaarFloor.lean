import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiniteVolumeLinkMassLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwoSidedTwelveColorDirichlet
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGlobalMeanPoincare
import Mathlib.Tactic

/-!
# P4-Q2-DG: genuine original Wilson twelve-color positive Haar fiber floor

CP proves that ONE finite-volume strictly positive original Perron-vacuum
fiber mass floor works for EVERY original RIGHT spatial link. BB's
original LEFT spatial link reference is literally the same original right
link reference applied after the genuine endpoint swap. Thus the SAME
physical density floor works simultaneously for every left/right link.

We lift those original-link inequalities through the EXACT six spatial
color partitions on both physical boundaries, preserving the true
color-cardinality inverses and the outer 1/12 normalization. In
particular, the ORIGINAL twelve-color Wilson Haar reference bounds an
explicit positive mass-weighted independent Haar fiber-variance energy.

This is a genuine finite-volume step toward connecting the already proved
DC independent pair-Haar Efron-Stein inequality and DF original physical
Wilson/pair-Haar variance comparison with the original Wilson full-joint
Riesz quadratic. The remaining bridge is exact identification of the
bounded Haar fiber-variance integrals with the genuine CR off-coordinate
Hilbert-L² residuals, plus the finite color-normalization comparison.
No Wilson conditional-projection commutation, new physical law, or volume-
uniform or continuum Yang--Mills mass-gap assertion enters here.
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

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Colors" => PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor

/-- The UNWEIGHTED genuine right-link Haar variance with exactly the
original Wilson coefficient and a fixed positive mass-floor parameter.
It is a reference integral on the actual outer Haar probability, not an
invented Wilson one-link conditional law. -/
noncomputable def p4Q2DG_rightHaarMassFloor
    (m : ℝ) (target : Link) (F : Joint → ℝ) : ENNReal :=
  ∫⁻ ctx,
    ENNReal.ofReal m *
      (ENNReal.ofReal (Real.exp (-32 * beta)) *
        evariance
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F ctx.1 ctx.2)
          (normalizedCompactHaar G))
    ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar G)))

/-- The same actual left-boundary Haar fiber variance is defined through
BB's genuine endpoint-swap map; no second mass hypothesis is inserted. -/
noncomputable def p4Q2DG_leftHaarMassFloor
    (m : ℝ) (target : Link) (F : Joint → ℝ) : ENNReal :=
  p4Q2DG_rightHaarMassFloor H N beta m target
    (p4Q2BB_swapConcrete H N F)

/-- ONE m(H,N,beta)>0 controls the genuine original Wilson twelve-color
Haar reference on BOTH endpoints and ALL actual right/left link positions.
The CP right-link theorem and BB exact original endpoint swap are sufficient.
-/
theorem p4Q2DG_originalBothEndpoints_linkHaarMassFloor :
    ∃ m : ℝ, 0 < m ∧
      ∀ (target : Link) (F : Joint → ℝ), StronglyMeasurable F →
        p4Q2DG_rightHaarMassFloor H N beta m target F ≤
          p4Q2AZ_originalJointHaarReferenceEnergy
            H N hN beta hbeta target F ∧
        p4Q2DG_leftHaarMassFloor H N beta m target F ≤
          p4Q2BB_originalLeftLinkHaarReferenceEnergy
            H N hN beta hbeta target F := by
  obtain ⟨m, hm, hright⟩ :=
    p4Q2CP_originalAllRightLinkHaarReference_ge_unweightedHaar
      H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  intro target F hF
  constructor
  · exact hright target F hF
  · change
      p4Q2DG_rightHaarMassFloor H N beta m target
        (p4Q2BB_swapConcrete H N F) ≤
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
    exact hright target (p4Q2BB_swapConcrete H N F)
      (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)

/-- Exact original six-color partition with the TRUE reciprocal
cardinality of each physical color. The right and left branches are
the same actual normalized link energies appearing in BB. -/
noncomputable def p4Q2DG_twelveColorHaarMassFloorAverage
    (m : ℝ) (c : Colors) (F : Joint → ℝ) : ENNReal :=
  match c with
  | Sum.inl k =>
      (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
        ∑ e : p4Q2BA_ColorLinks H k,
          p4Q2DG_rightHaarMassFloor H N beta m e.1 F
  | Sum.inr k =>
      (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
        ∑ e : p4Q2BA_ColorLinks H k,
          p4Q2DG_leftHaarMassFloor H N beta m e.1 F

/-- Preserve the original twelve-color average, with the EXACT factor
1/12 and every original color-block cardinality (no unnormalized sum
is substituted for the physical reference operator). -/
noncomputable def p4Q2DG_originalTwelveColorHaarMassFloor
    (m : ℝ) (F : Joint → ℝ) : ENNReal :=
  (12 : ENNReal)⁻¹ *
    ∑ c : Colors, p4Q2DG_twelveColorHaarMassFloorAverage H N beta m c F

/-- At a fixed actual original physical link-mass floor, each right/left
physical color energy controls the honest same-color Haar reference. -/
theorem p4Q2DG_twelveColorMassFloor_le_originalReferenceAverage
    (m : ℝ)
    (hlinks : ∀ (target : Link) (F : Joint → ℝ),
      StronglyMeasurable F →
      p4Q2DG_rightHaarMassFloor H N beta m target F ≤
        p4Q2AZ_originalJointHaarReferenceEnergy
          H N hN beta hbeta target F ∧
      p4Q2DG_leftHaarMassFloor H N beta m target F ≤
        p4Q2BB_originalLeftLinkHaarReferenceEnergy
          H N hN beta hbeta target F)
    (c : Colors) (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    p4Q2DG_twelveColorHaarMassFloorAverage H N beta m c F ≤
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F := by
  classical
  cases c with
  | inl k =>
      change
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H k,
            p4Q2DG_rightHaarMassFloor H N beta m e.1 F) ≤
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k F
      exact mul_le_mul_left'
        (Finset.sum_le_sum (fun e _he => (hlinks e.1 F hF).1))
        _
  | inr k =>
      change
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H k,
            p4Q2DG_leftHaarMassFloor H N beta m e.1 F) ≤
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k F
      exact mul_le_mul_left'
        (Finset.sum_le_sum (fun e _he => (hlinks e.1 F hF).2))
        _

/-- Genuine ORIGINAL Wilson twelve-color Haar reference dominates a
SINGLE positive-finite-volume weighted sum of EVERY independent Haar
right/left link variance on the actual original spatial carrier. -/
theorem p4Q2DG_originalTwelveColorHaarReference_ge_allLinkMassFloor :
    ∃ m : ℝ, 0 < m ∧
      ∀ (F : Joint → ℝ), StronglyMeasurable F →
        p4Q2DG_originalTwelveColorHaarMassFloor H N beta m F ≤
          p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F := by
  obtain ⟨m, hm, hlink⟩ :=
    p4Q2DG_originalBothEndpoints_linkHaarMassFloor
      H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  intro F hF
  unfold p4Q2DG_originalTwelveColorHaarMassFloor
    p4Q2BC_originalPhysicalTwelveColorHaarReference
  exact mul_le_mul_left'
    (Finset.sum_le_sum (fun c _hc =>
      p4Q2DG_twelveColorMassFloor_le_originalReferenceAverage
        H N hN beta hbeta m hlink c F hF))
    _

end OriginalWilson

end MathlibAnalytic
end MGAP4D
