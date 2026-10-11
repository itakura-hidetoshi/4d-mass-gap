import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonOuterVarianceMeasurability
import Mathlib.Tactic

/-!
# P4-Q2-BM: literal original Wilson one-link Haar reference parallelogram

BJ proved the original Haar fiber variance parallelogram pointwise, BK
the outer integration with precisely stated AEMeasurable premises, and
BL discharged both premises for the actual Wilson joint law.

This file instantiates that chain on the true original Wilson
ground-state left-Haar × right-off-target Haar outer carrier.
It retains exactly the original split-target fiber mass and e^(-32 beta),
with no surrogate measure, independence assumption or link-count penalty.

For every pair of bounded strongly measurable concrete original Wilson
joint observables F, G, the REAL one-link mass-weighted reference obeys
the ENNReal parallelogram identity. This is not a reverse Poincare bound
and does not assert the one-link quadratic form is coercive.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000
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
variable (target : PeriodicHypercubicEvenSpatialSliceLink H)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "SU" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Ctx" => p4Q2BL_originalOuterType H N target

/-- First unconditional outer-integrated parallelogram for the LITERAL
original physical Wilson right one-link mass-weighted Haar reference.
The only finite-function premises are the original strongly measurable
bounded concrete joint observations (needed for Haar L²). -/
theorem p4Q2BM_originalJointOneLinkHaarReference_parallelogram
    (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta
        target (fun z => F z + G z) +
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta
        target (fun z => F z - G z) =
      (2 : ENNReal) *
        (p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target F +
          p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target G) := by
  let μLink : Measure SU := normalizedCompactHaar SU
  letI : IsProbabilityMeasure μLink := by
    dsimp [μLink]
    infer_instance
  let μOuter : Measure Ctx :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ :
        PeriodicHypercubicEvenSpatialSliceOffTargetLink H target => μLink))
  let weight : Ctx → ENNReal :=
    fun ctx =>
      periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
        H N hN beta hbeta target ctx *
        ENNReal.ofReal (Real.exp (-32 * beta))
  let XF : Ctx → SU → ℝ := fun ctx u =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F ctx.1 ctx.2 u
  let XG : Ctx → SU → ℝ := fun ctx u =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target G ctx.1 ctx.2 u
  have hXF : ∀ ctx : Ctx, MemLp (XF ctx) 2 μLink := by
    intro ctx
    exact p4Q2BJ_originalJointOneLinkSection_memLp
      H N target F hF boundF hboundF ctx.1 ctx.2
  have hXG : ∀ ctx : Ctx, MemLp (XG ctx) 2 μLink := by
    intro ctx
    exact p4Q2BJ_originalJointOneLinkSection_memLp
      H N target G hG boundG hboundG ctx.1 ctx.2
  have hPlus0 :=
    p4Q2BL_originalJointHaarReferenceIntegrand_aemeasurable
      H N hN beta hbeta target (fun z => F z + G z) (hF.add hG)
  have hPlus :
      AEMeasurable
        (fun ctx : Ctx =>
          weight ctx * evariance (fun u => XF ctx u + XG ctx u) μLink)
        μOuter := by
    change AEMeasurable
      (fun ctx : Ctx =>
        weight ctx *
          evariance
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target (fun z => F z + G z) ctx.1 ctx.2)
            μLink) μOuter at hPlus0
    simpa only [p4Q2BJ_originalJointOneLinkSection_add] using hPlus0
  have hMeasF :
      AEMeasurable
        (fun ctx : Ctx => weight ctx * evariance (XF ctx) μLink)
        μOuter := by
    simpa only [XF, μLink, μOuter, weight] using
      (p4Q2BL_originalJointHaarReferenceIntegrand_aemeasurable
        H N hN beta hbeta target F hF)
  have hBK :=
    p4Q2BK_weightedHaarFiberVariance_parallelogram
      μOuter μLink weight XF XG hXF hXG hPlus hMeasF
  have hRep (K : Joint → ℝ) :
      p4Q2AZ_originalJointHaarReferenceEnergy
          H N hN beta hbeta target K =
        p4Q2BH_weightedHaarFiberVariance μOuter μLink weight
          (fun (ctx : Ctx) (u : SU) =>
            periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target K ctx.1 ctx.2 u) := by
    simp only [
      p4Q2AZ_originalJointHaarReferenceEnergy,
      p4Q2BH_weightedHaarFiberVariance, μOuter, μLink, weight, mul_assoc]
  have hPlusEq :
      (fun (ctx : Ctx) (u : SU) =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => F z + G z) ctx.1 ctx.2 u) =
      (fun ctx u => XF ctx u + XG ctx u) := by
    funext ctx u
    exact congrFun
      (p4Q2BJ_originalJointOneLinkSection_add
        H N target F G ctx.1 ctx.2) u
  have hMinusEq :
      (fun (ctx : Ctx) (u : SU) =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => F z - G z) ctx.1 ctx.2 u) =
      (fun ctx u => XF ctx u - XG ctx u) := by
    funext ctx u
    exact congrFun
      (p4Q2BJ_originalJointOneLinkSection_sub
        H N target F G ctx.1 ctx.2) u
  rw [hRep (fun z => F z + G z),
    hRep (fun z => F z - G z), hRep F, hRep G,
    hPlusEq, hMinusEq]
  exact hBK

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
