import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLeftFiberUnswappedHilbertDefect
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorPositiveHaarFloor
import Mathlib.Tactic

/-!
# P4-Q2-DO: positive original Wilson link mass floors as true L² defects

DG proves one STRICTLY positive finite-volume original Wilson
Perron-vacuum fiber mass floor for ALL genuine physical right and left
links and the exact twelve-color normalized reference energy lower bound.

DK and DN identify the original Wilson right and left UNWEIGHTED Haar
fiber variance integrals with the unswapped true CR physical pair-Haar
coordinate Hilbert-L² defect squared, respectively.

This file uses the existing pinned mathlib `lintegral_const_mul'`
(and its explicit non-top conditions) to pull out the genuine common
finite-volume m and original factor exp(-32 beta), without modifying
physical measures or treating Wilson conditional means as independent.

For EVERY bounded strongly measurable original physical joint
observable F represented a.e. by its true pair-Haar Hilbert class f:

   DG.rightFloor(m,F,link) =
      ofReal(m) * (ofReal(exp(-32 beta)) *
        ofReal(‖f - P_right,link f‖²))

   DG.leftFloor(m,F,link) =
      ofReal(m) * (ofReal(exp(-32 beta)) *
        ofReal(‖f - P_left,link f‖²))

No new positive beta projection commutativity. The next quantitative
steps sum these exact identities with the true physical 12-color
normalization, derive finite-volume original Wilson coercivity, and
separately address volume-uniform/continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

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

/-- Two finite (not-top) nonnegative scalar factors may be pulled
outside the genuine extended nonnegative Haar integral WITHOUT
asserting pointwise fiber representative measurability. -/
private theorem p4Q2DO_double_constant_lintegral
    {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (a b : ENNReal)
    (ha : a ≠ ∞) (hb : b ≠ ∞) (g : A → ENNReal) :
    (∫⁻ z, a * (b * g z) ∂μ) =
      a * (b * (∫⁻ z, g z ∂μ)) := by
  calc
    (∫⁻ z, a * (b * g z) ∂μ) =
        a * (∫⁻ z, b * g z ∂μ) :=
      lintegral_const_mul' a _ ha
    _ = a * (b * (∫⁻ z, g z ∂μ)) :=
      congrArg (fun v : ENNReal => a * v)
        (lintegral_const_mul' b g hb)

section OriginalWilson
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "muH" => normalizedCompactHaar G
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- The actual original Wilson right/left reference uses the same
left-boundary-Haar × off-target-right-Haar context probability. -/
private noncomputable def p4Q2DO_originalRightOuterHaar
    (target : Link) :
    Measure (Cfg ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G)) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target => muH))

/-- The actual original Wilson RIGHT link mass floor is exactly the
positive original coefficient times its true pair-Haar Hilbert CR
right-coordinate defect squared, on bounded physical observables. -/
theorem p4Q2DO_originalRightHaarMassFloor_eq_CR_defect
    (m : ℝ) (target : Link) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    p4Q2DG_rightHaarMassFloor H N beta m target F =
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f - P (Sum.inr target) f‖ ^ 2)) := by
  let μouter := p4Q2DO_originalRightOuterHaar H N target
  have hVariance :
      (∫⁻ ctx : Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
        evariance (Section target F ctx.1 ctx.2) muH ∂μouter) =
          ENNReal.ofReal (‖f - P (Sum.inr target) f‖ ^ 2) := by
    simpa [μouter, p4Q2DO_originalRightOuterHaar] using
      (p4Q2DK_originalRightHaarFiberVariance_eq_CR_defect
        H N target f F hF M hM hEq)
  have hFactor :=
    p4Q2DO_double_constant_lintegral μouter
      (ENNReal.ofReal m) (ENNReal.ofReal (Real.exp (-32 * beta)))
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (fun ctx : Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G) =>
        evariance (Section target F ctx.1 ctx.2) muH)
  change
    (∫⁻ ctx : Cfg ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          evariance (Section target F ctx.1 ctx.2) muH)
      ∂μouter) =
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f - P (Sum.inr target) f‖ ^ 2))
  rw [hFactor, hVariance]

/-- SAME original physical finite-volume coefficient on the LEFT link:
the reference fiber is the actual boundary-swap observable, while the
Hilbert defect is in the UNSWAPPED original left-coordinate sector. -/
theorem p4Q2DO_originalLeftHaarMassFloor_eq_CR_defect
    (m : ℝ) (target : Link) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    p4Q2DG_leftHaarMassFloor H N beta m target F =
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f - P (Sum.inl target) f‖ ^ 2)) := by
  let μouter := p4Q2DO_originalRightOuterHaar H N target
  have hVariance :
      (∫⁻ ctx : Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
        evariance
          (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
          muH ∂μouter) =
        ENNReal.ofReal (‖f - P (Sum.inl target) f‖ ^ 2) := by
    simpa [μouter, p4Q2DO_originalRightOuterHaar] using
      (p4Q2DN_originalLeftHaarFiberVariance_eq_CR_left_defect
        H N target f F hF M hM hEq)
  have hFactor :=
    p4Q2DO_double_constant_lintegral μouter
      (ENNReal.ofReal m) (ENNReal.ofReal (Real.exp (-32 * beta)))
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (fun ctx : Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G) =>
        evariance
          (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2) muH)
  change
    (∫⁻ ctx : Cfg ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          evariance
            (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
            muH)
      ∂μouter) =
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f - P (Sum.inl target) f‖ ^ 2))
  rw [hFactor, hVariance]

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
