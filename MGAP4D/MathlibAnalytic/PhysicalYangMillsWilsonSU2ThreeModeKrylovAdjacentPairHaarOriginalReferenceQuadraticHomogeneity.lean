import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveColorBilinearCarrier
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# P4-Q2-BH: original Wilson Haar fiber variance quadratic homogeneity

The source is the literal mass-weighted original Wilson ground-state right
one-link Haar reference energy, not the physical conditional expectation
Dirichlet energy introduced in BG.

At the pinned mathlib SHA, `ProbabilityTheory.evariance_mul` holds without
an L² integrability premise in extended nonnegative reals. Likewise,
`MeasureTheory.lintegral_const_mul'` moves the finite coefficient outside a
nonnegative integral without a separate measurability hypothesis.

We first isolate their purely algebraic weighted-fiber principle, then apply
it to the actual original Wilson outer Haar product, unchanged original
ground-state fiber mass, exp(-32 beta) local coefficient, and literal link
section. No surrogate physical law, fiber mass floor, or link independence
is introduced.

This establishes genuine original-reference quadratic scaling, NOT
bilinearity or a reverse Poincare inequality.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000

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

/-- The algebraic scalar-variance integration principle, parametrized by the
actual measures and nonnegative weight supplied by the caller. -/
noncomputable def p4Q2BH_weightedHaarFiberVariance
    {Outer Gauge : Type*}
    [MeasurableSpace Outer] [MeasurableSpace Gauge]
    (μOuter : Measure Outer) (μHaar : Measure Gauge)
    (weight : Outer → ENNReal)
    (fiberFn : Outer → Gauge → ℝ) : ENNReal :=
  ∫⁻ ctx, weight ctx * evariance (fiberFn ctx) μHaar ∂μOuter

/-- Homogeneity in the ORIGINAL fiber observable does not require dividing by
fiber mass or interchanging noncommuting physical projections. -/
theorem p4Q2BH_weightedHaarFiberVariance_mul
    {Outer Gauge : Type*}
    [MeasurableSpace Outer] [MeasurableSpace Gauge]
    (μOuter : Measure Outer) (μHaar : Measure Gauge)
    (weight : Outer → ENNReal)
    (fiberFn : Outer → Gauge → ℝ) (a : ℝ) :
    p4Q2BH_weightedHaarFiberVariance μOuter μHaar weight
      (fun ctx u => a * fiberFn ctx u) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2BH_weightedHaarFiberVariance μOuter μHaar weight fiberFn := by
  unfold p4Q2BH_weightedHaarFiberVariance
  simp_rw [ProbabilityTheory.evariance_mul]
  calc
    (∫⁻ ctx, weight ctx *
        (ENNReal.ofReal (a ^ 2) * evariance (fiberFn ctx) μHaar) ∂μOuter) =
        ∫⁻ ctx, ENNReal.ofReal (a ^ 2) *
          (weight ctx * evariance (fiberFn ctx) μHaar) ∂μOuter := by
          apply lintegral_congr
          intro ctx
          ac_rfl
    _ = ENNReal.ofReal (a ^ 2) *
        (∫⁻ ctx, weight ctx * evariance (fiberFn ctx) μHaar ∂μOuter) := by
          exact lintegral_const_mul'
            (ENNReal.ofReal (a ^ 2))
            (fun ctx => weight ctx * evariance (fiberFn ctx) μHaar)
            ENNReal.ofReal_lt_top.ne

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin N) ℂ

/-- The literal original right-link section commutes with scalar
multiplication of the concrete joint observable, pointwise on the same link. -/
theorem p4Q2BH_originalJointOneLinkConcreteSection_mul
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (a : ℝ) (F : Joint → ℝ)
    (left : Cfg)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target (fun z => a * F z) left retained =
      (fun u : Gauge => a *
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained u) := by
  funext u
  rfl

/-- Exact quadratic scaling of ONE actual original Wilson mass-weighted
one-link Haar reference, including its original outer Haar carrier, fiber
mass and exp(-32 beta) local comparison factor. -/
theorem p4Q2BH_originalJointOneLinkHaarReference_mul
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (a : ℝ) (F : Joint → ℝ) :
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta
        target (fun z => a * F z) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target F := by
  let μLink : Measure Gauge := normalizedCompactHaar Gauge
  let μOuter : Measure
      (Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge)) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        μLink))
  let weight :
      (Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge)) →
          ENNReal :=
    fun ctx =>
      periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
        H N hN beta hbeta target ctx *
        ENNReal.ofReal (Real.exp (-32 * beta))
  have hrepr (G : Joint → ℝ) :
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target G =
        p4Q2BH_weightedHaarFiberVariance μOuter μLink weight
          (fun (ctx : Cfg ×
              (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge))
            (u : Gauge) =>
            periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target G ctx.1 ctx.2 u) := by
    simp only [
      p4Q2AZ_originalJointHaarReferenceEnergy,
      p4Q2BH_weightedHaarFiberVariance, μOuter, μLink, weight, mul_assoc]
  rw [hrepr (fun z => a * F z), hrepr F]
  have hsection :
      (fun (ctx : Cfg ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge))
        (u : Gauge) =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => a * F z) ctx.1 ctx.2 u) =
      (fun (ctx : Cfg ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge))
        (u : Gauge) =>
        a * periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F ctx.1 ctx.2 u) := by
    funext ctx u
    exact congrFun
      (p4Q2BH_originalJointOneLinkConcreteSection_mul
        H N target a F ctx.1 ctx.2) u
  rw [hsection]
  exact p4Q2BH_weightedHaarFiberVariance_mul
    μOuter μLink weight
    (fun (ctx : Cfg ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge))
      (u : Gauge) =>
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F ctx.1 ctx.2 u) a

/-- The exact original ground-state right all-link color sum also scales
quadratically, without an added factor counting the links. -/
theorem p4Q2BH_originalRightColorAllLinkReference_mul
    (c : Fin 6) (a : ℝ) (F : Joint → ℝ) :
    p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
        (fun z => a * F z) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2BA_colorAllLinkHaarReferenceSum
          H N hN beta hbeta c F := by
  unfold p4Q2BA_colorAllLinkHaarReferenceSum
  simp_rw [
    p4Q2BH_originalJointOneLinkHaarReference_mul
      H N hN beta hbeta]
  rw [Finset.mul_sum]

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
