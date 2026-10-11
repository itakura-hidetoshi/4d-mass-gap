import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullL2QualitativeKernelCollapse
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalContinuousDensityFiniteVolumeSandwich
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAELinkHaarFiberZero
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitContextCoordinateEquiv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-CP: genuine Wilson original positive finite-volume fiber-mass floor

CO established exact qualitative kernel equality on the ORIGINAL physical
joint L². To approach quantitative coercivity, we start with the missing
positive *finite-volume* lower bound for the physical ONE-LINK mass
that appears LITERALLY in the original 12-color Wilson Haar reference.

CD gives a strictly positive global minimum m on the compact joint
configuration space for the ACTUAL continuous Perron-vacuum density.
AU proves the old physical Wilson density is equal to this continuous
density only pair-Haar-almost everywhere. We transport that a.e. identity
through the certified measure-preserving original right-link Haar split,
apply Fubini, and integrate the inequality on the singleton Haar target.

The SAME positive finite-volume m works for EVERY genuine spatial link;
we do not replace the old physical density by a fictitious pointwise
representative on exceptional fibers. Thus every actual positive-β
mass-weighted Haar reference dominates a non-mass-weighted Haar variance
integral at the genuine local factor m * exp(-32 β).

This is a new positive local quantitative ingredient, NOT YET a reverse
Poincare inequality on all L² or a volume-uniform spectral gap. The
constant depends on H, N and beta.
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

/-- Integrating an a.e. positive floor over a probability target fiber
preserves the SAME floor for almost every outer context. -/
private theorem p4Q2CP_fiberMass_floor_of_ae_product
    {Ctx G : Type*} [MeasurableSpace Ctx] [MeasurableSpace G]
    (μ : Measure Ctx) (ν : Measure G) [IsProbabilityMeasure ν]
    (density : Ctx → G → ENNReal) (m : ENNReal)
    (h : ∀ᵐ ctx ∂μ, ∀ᵐ g ∂ν, m ≤ density ctx g) :
    ∀ᵐ ctx ∂μ, m ≤ ∫⁻ g, density ctx g ∂ν := by
  filter_upwards [h] with ctx hctx
  have hi :
      (∫⁻ g : G, m ∂ν) ≤ ∫⁻ g, density ctx g ∂ν :=
    lintegral_mono_ae hctx
  simpa using hi

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "wRaw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    H N hN beta hbeta
local notation "wCont" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H N hN beta hbeta
local notation "Mass" =>
  periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    H N hN beta hbeta

/-- A SINGLE strictly positive finite-volume floor works for the real
physical mass of EVERY original right spatial SU(N) Haar target fiber.
The old physical Wilson density equals the continuous vacuum density only
almost everywhere, and the conclusion correctly preserves this qualifier. -/
theorem p4Q2CP_originalEveryRightLinkMass_ae_pos_floor :
    ∃ m : ℝ, 0 < m ∧
      ∀ target : Link,
        ∀ᵐ ctx ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar G))),
          ENNReal.ofReal m ≤ Mass target ctx := by
  obtain ⟨m, M, hm, hbounds⟩ :=
    p4Q2CD_originalWilsonContinuousJointDensity_exists_pos_uniform_bounds
      H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  intro target
  classical
  let Ctx := Cfg ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G)
  let TargetCfg := PeriodicHypercubicEvenSpatialSliceTargetLink H target → G
  let μOuter : Measure Ctx :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar G))
  let μTarget : Measure TargetCfg :=
    Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar G)
  letI : IsProbabilityMeasure μTarget := by
    dsimp [μTarget]
    infer_instance
  let e :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  have he : MeasurePreserving e (μOuter.prod μTarget) μPair := by
    simpa [e, μOuter, μTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H N target)
  have hglobal :
      (fun z : Joint => ENNReal.ofReal (wRaw z)) =ᵐ[μPair]
        (fun z : Joint => ENNReal.ofReal (wCont z)) := by
    filter_upwards
      [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuous
        H N hN beta hbeta] with z hz
    exact congrArg ENNReal.ofReal hz
  have hpull := he.quasiMeasurePreserving.ae_eq hglobal
  have hsplit :
      (fun z : Ctx × TargetCfg =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
          H N hN beta hbeta z.1.1 target (z.2, z.1.2)) =ᵐ[μOuter.prod μTarget]
        (fun z : Ctx × TargetCfg => ENNReal.ofReal (wCont (e z))) := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv_apply,
      e, Function.comp_def] using hpull
  have hpoint :
      ∀ᵐ z ∂(μOuter.prod μTarget),
        ENNReal.ofReal m ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta z.1.1 target (z.2, z.1.2) := by
    filter_upwards [hsplit] with z hz
    calc
      ENNReal.ofReal m ≤ ENNReal.ofReal (wCont (e z)) :=
        ENNReal.ofReal_le_ofReal (hbounds (e z)).1
      _ = _ := hz.symm
  have hnested :
      ∀ᵐ ctx ∂μOuter, ∀ᵐ t ∂μTarget,
        ENNReal.ofReal m ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta ctx.1 target (t, ctx.2) :=
    Measure.ae_ae_of_ae_prod hpoint
  have hmass :=
    p4Q2CP_fiberMass_floor_of_ae_product μOuter μTarget
      (fun ctx t =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
          H N hN beta hbeta ctx.1 target (t, ctx.2))
      (ENNReal.ofReal m) hnested
  simpa [μOuter,
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass,
    μTarget] using hmass

/-- The original ACTUAL right Wilson one-link mass-weighted Haar energy
dominates the UNWEIGHTED genuine Haar-link variance, with the same
strictly positive finite-volume coefficient for ALL right links.

The right-hand side is the LITERAL original P4-Q2-AZ Wilson reference.
The Haar law on the left is the original split pair-Haar law, not a
physical conditional posterior or beta-zero substitute. -/
theorem p4Q2CP_originalAllRightLinkHaarReference_ge_unweightedHaar :
    ∃ m : ℝ, 0 < m ∧
      ∀ target : Link,
        ∀ (F : Joint → ℝ), StronglyMeasurable F →
          (∫⁻ ctx,
              ENNReal.ofReal m *
                (ENNReal.ofReal (Real.exp (-32 * beta)) *
                  evariance
                    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                      H N target F ctx.1 ctx.2)
                    (normalizedCompactHaar G))
              ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
                (Measure.pi
                  (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                    normalizedCompactHaar G)))) ≤
          p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target F := by
  obtain ⟨m, hm, hmass⟩ :=
    p4Q2CP_originalEveryRightLinkMass_ae_pos_floor H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  intro target F hF
  change
    (∫⁻ ctx,
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          evariance
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F ctx.1 ctx.2)
            (normalizedCompactHaar G))
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar G)))) ≤
      (∫⁻ ctx,
        Mass target ctx *
          (ENNReal.ofReal (Real.exp (-32 * beta)) *
            evariance
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F ctx.1 ctx.2)
              (normalizedCompactHaar G))
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar G))))
  apply lintegral_mono_ae
  filter_upwards [hmass target] with ctx hctx
  exact mul_le_mul_left hctx _

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
