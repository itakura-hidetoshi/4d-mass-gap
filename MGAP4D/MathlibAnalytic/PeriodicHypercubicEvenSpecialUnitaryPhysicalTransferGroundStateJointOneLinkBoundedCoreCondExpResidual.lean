import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExp
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkOriginalCoordinateMarkovIdentity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointOneLinkBoundedCoreResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointOneLinkBoundedCoreResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointOneLinkBoundedCoreResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointOneLinkBoundedCoreResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointOneLinkBoundedCoreResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointOneLinkBoundedCoreResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateJointOneLinkBoundedCoreResidualTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance groundStateJointOneLinkBoundedCoreResidualTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- The weighted singleton-target centered residual of a concrete observable is
exactly the original-coordinate squared residual integrated against the genuine
ground-state joint law.  This is a measure/integration identity only: it makes
no RCD or conditional-law identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional_eq_joint_lintegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (C :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target → ℝ)
    (hC : StronglyMeasurable C) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C =
      ∫⁻ z,
        ENNReal.ofReal
          ((F z -
              C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z)) ^ 2)
        ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let outer :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
      H N target
  let G :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ENNReal :=
    fun left right =>
      ENNReal.ofReal ((F (left, right) - C (outer (left, right))) ^ 2)
  have houter : Measurable outer := by
    simpa [outer] using
      (measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N target)
  have hResidual : StronglyMeasurable (fun z => F z - C (outer z)) :=
    hF.sub (hC.comp_measurable houter)
  have hSquare : StronglyMeasurable (fun z => (F z - C (outer z)) ^ 2) := by
    simpa [pow_two] using hResidual.mul hResidual
  have hGMeas : Measurable (Function.uncurry G) := by
    simpa [G, Function.uncurry] using hSquare.measurable.ennreal_ofReal
  have hG : AEMeasurable (Function.uncurry G) (μ.prod μ) :=
    hGMeas.aemeasurable
  obtain ⟨κ, hκ, hκae, hidentity⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointTarget_exists_markovKernel_original_lintegral_identity
      H N hN beta hbeta target G (by simpa [μ] using hG)
  letI : IsMarkovKernel κ := hκ
  let Gsplit :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ENNReal :=
    fun ctx targetCfg => G ctx.1 (split.symm (targetCfg, ctx.2))
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  have hGsplitMeas : Measurable (Function.uncurry Gsplit) := by
    have hcomp := hGMeas.comp coord.measurable
    simpa [Gsplit, coord, split, Function.comp_def, Function.uncurry] using hcomp
  have hInner : Measurable (fun ctx => ∫⁻ targetCfg, Gsplit ctx targetCfg ∂κ ctx) :=
    hGsplitMeas.lintegral_kernel_prod_right'
  let Z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ENNReal :=
    fun ctx =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
        H N hN beta hbeta ctx.1 target ctx.2
  have hSplitDensity :
      AEMeasurable
        (fun z :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
                  Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
              (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta z.1.1 target (z.2, z.1.2))
        ((μ.prod μOff).prod μTarget) := by
    simpa [μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
        H N hN beta hbeta target)
  have hZ : AEMeasurable Z (μ.prod μOff) := by
    simpa [Z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass]
      using hSplitDensity.lintegral_prod_right'
  let RK := fun ctx => Z ctx * ∫⁻ targetCfg, Gsplit ctx targetCfg ∂κ ctx
  let R := fun ctx =>
    Z ctx *
      doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2)
        (fun targetCfg =>
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F ctx.1 ctx.2 (eval targetCfg))
        (C ctx)
  have hRK : AEMeasurable RK (μ.prod μOff) := by
    exact hZ.mul hInner.aemeasurable
  have hOffTarget :
      ∀ (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)
        (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target
            (split.symm (targetCfg, retained)) = retained := by
    intro targetCfg retained
    simpa [split] using
      congrArg Prod.snd (split.apply_symm_apply (targetCfg, retained))
  have hOuterSplit :
      ∀ (ctx :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))
        (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ),
        outer (ctx.1, split.symm (targetCfg, ctx.2)) = ctx := by
    intro ctx targetCfg
    apply Prod.ext
    · rfl
    · exact hOffTarget targetCfg ctx.2
  have hSectionSplit :
      ∀ (ctx :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))
        (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F ctx.1 ctx.2 (eval targetCfg) =
          F (ctx.1, split.symm (targetCfg, ctx.2)) := by
    intro ctx targetCfg
    simp [periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
      eval, split]
  have hRK_R : RK =ᵐ[μ.prod μOff] R := by
    filter_upwards [hκae] with ctx hκctx
    dsimp [RK, R]
    rw [hκctx]
    congr 1
    unfold doobCenteredSquaredResidual
    apply lintegral_congr
    intro targetCfg
    rw [hSectionSplit ctx targetCfg]
    simp [Gsplit, G, hOuterSplit ctx targetCfg]
  have hR : AEMeasurable R (μ.prod μOff) :=
    hRK.congr hRK_R
  have hCentered :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
          H N hN beta hbeta target F C =
        ∫⁻ ctx, R ctx ∂(μ.prod μOff) := by
    change
      (∫⁻ left,
        ∫⁻ retained,
          R (left, retained) ∂μOff ∂μ) =
        ∫⁻ ctx, R ctx ∂(μ.prod μOff)
    rw [lintegral_prod _ hR]
  have hDensity :
      AEMeasurable
        (fun z => ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta z))
        (μ.prod μ) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hJoint :
      (∫⁻ z,
          G z.1 z.2
          ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)) =
        ∫⁻ z,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
              H N hN beta hbeta z.1 z.2 *
            G z.1 z.2
          ∂(μ.prod μ) := by
    change
      (∫⁻ z, G z.1 z.2
        ∂(μ.prod μ).withDensity
          (fun z => ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
              H N hN beta hbeta z))) =
        ∫⁻ z,
          ENNReal.ofReal
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
                H N hN beta hbeta z) *
            G z.1 z.2
          ∂(μ.prod μ)
    rw [lintegral_withDensity_eq_lintegral_mul₀ hDensity hG]
    rfl
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C =
      ∫⁻ ctx, R ctx ∂(μ.prod μOff) := hCentered
    _ = ∫⁻ ctx, RK ctx ∂(μ.prod μOff) :=
      lintegral_congr_ae hRK_R.symm
    _ = ∫⁻ z,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
              H N hN beta hbeta z.1 z.2 *
            G z.1 z.2
          ∂(μ.prod μ) := by
      simpa [RK, Gsplit, Z, μ, μOff, split] using hidentity.symm
    _ = ∫⁻ z,
          G z.1 z.2
          ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) := hJoint.symm
    _ = ∫⁻ z,
          ENNReal.ofReal
            ((F z -
                C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target z)) ^ 2)
          ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
