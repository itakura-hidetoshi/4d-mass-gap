import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOneLinkHilbertProjectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# P4-Q2-AZ: original physical Wilson local Dirichlet energy on the six-color core

AX integrated the actual ground-state one-link fiber inequality for an
outer-independent bounded continuous SU(N) observable; AY identified its
physical Hilbert projection residual on the corresponding cylinder core.

Here the AW *outer-almost-everywhere, all-observables* theorem is used at
each good context on the actual section of an ARBITRARY bounded, strongly
measurable concrete joint observable F. The exact original split-target
fiber mass remains unchanged. The resulting physical one-link lower bound
is lifted through the already-proved canonical Markov disintegration and
CondExpL2 residual identity.

For a chosen link of each of the six spatial colors, the local lower bounds
can then be summed against the genuine six-color block projection residuals,
without asserting same-color commutation, spatial independence, any uniform
outer fiber mass bound, or a global uniform physical spectral gap.

The normalized right-six-color residual is an upper bound for the average
selected-link Haar reference Dirichlet form; the MISSING reverse
dependent-link/frame coercivity remains a separate obstruction.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 2600000
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

/-- A concrete bounded joint function defines a vector in the ORIGINAL
physical Wilson joint L2, without evaluating an L2 quotient on a fiber. -/
noncomputable def p4Q2AZ_originalJointL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta F hF bound hbound

/-- The actual original physical split-fiber mass and the original
direct SU(N) link section of F, with the Wilson local factor exp(-32 beta).
The integration is on the actual left-Haar × off-target-Haar outer carrier. -/
noncomputable def p4Q2AZ_originalJointHaarReferenceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ENNReal :=
  let muOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  let muLink := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  ∫⁻ ctx,
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
      H N hN beta hbeta target ctx *
      (ENNReal.ofReal (Real.exp (-32 * beta)) *
        evariance
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F ctx.1 ctx.2)
          muLink)
    ∂muOuter

/-- Same literal original Wilson weighted physical conditional energy with
context-dependent sections, before the canonical Markov identification. -/
noncomputable def p4Q2AZ_originalJointIntegratedConditionalEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ENNReal :=
  let muOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  ∫⁻ ctx,
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
      H N hN beta hbeta target ctx *
      evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F ctx.1 ctx.2)
        (Measure.map eval
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta ctx.1 target ctx.2))
    ∂muOuter

/-- Full bounded joint-observable generalization of AX. The crucial AW
quantifier is outer-a.e. followed by EVERY link test function: the section
is chosen AFTER fixing each good outer context. No uniform positivity or
regular-conditional-law assertion at exceptional contexts is required. -/
theorem p4Q2AZ_originalJointIntegratedConditionalEnergy_ge_Haar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target F ≤
      p4Q2AZ_originalJointIntegratedConditionalEnergy H N hN beta hbeta target F := by
  classical
  let muOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  let muLink := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let mass := periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    H N hN beta hbeta target
  let section := fun ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F ctx.1 ctx.2
  let physical := fun ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    evariance (section ctx)
      (Measure.map eval
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2))
  let reference := fun ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    evariance (section ctx) muLink
  let coefficient := ENNReal.ofReal (Real.exp (-32 * beta))
  have hAW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalGroundStateSplitTargetFiber_ae_evariance_ge_Haar
      H N hN beta hbeta target
  have hPoint : ∀ᵐ ctx ∂muOuter,
      coefficient * reference ctx ≤ physical ctx := by
    filter_upwards [hAW] with ctx hctx
    let right := periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion
      H N target ctx.2
    have hOff :
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = ctx.2 :=
      periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion_offTarget
        H N target ctx.2
    let Xctx := section ctx
    have hMeas : StronglyMeasurable Xctx := by
      exact periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF ctx.1 ctx.2
    have hBound : ∀ g, ‖Xctx g‖ ≤ bound := by
      intro g
      simpa [Xctx, section,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection] using
        (hbound (ctx.1,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
              ctx.2)))
    have hHaar : MemLp Xctx 2 muLink := by
      letI : IsProbabilityMeasure muLink := by dsimp [muLink]; infer_instance
      exact MemLp.of_bound hMeas.aestronglyMeasurable bound
        (Filter.Eventually.of_forall hBound)
    let muRaw := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
      H N beta ctx.1 right target
    letI : IsProbabilityMeasure muRaw :=
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_probability
        H N beta ctx.1 right target
    have hRaw : MemLp Xctx 2 muRaw :=
      MemLp.of_bound hMeas.aestronglyMeasurable bound
        (Filter.Eventually.of_forall hBound)
    exact hctx right hOff Xctx hHaar hRaw
  change
    (∫⁻ ctx, mass ctx * (coefficient * reference ctx) ∂muOuter) ≤
      ∫⁻ ctx, mass ctx * physical ctx ∂muOuter
  exact p4Q2AX_massWeightedLIntegral_mono_of_ae
    muOuter mass reference physical coefficient hPoint

/-- The original context-integrated physical energy is below the canonical
original Markov fiber variance. Product-to-iterated Tonelli is used only in
the inequality direction, while canonical and historical fibers agree a.e. -/
theorem p4Q2AZ_originalJointIntegratedConditionalEnergy_le_canonicalVariance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    p4Q2AZ_originalJointIntegratedConditionalEnergy H N hN beta hbeta target F ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
  classical
  let muLeft := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let muOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let kappa :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  let nu := fun ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
      H N hN beta hbeta ctx.1 target ctx.2
  let mass := periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    H N hN beta hbeta target
  let section := fun (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retained
  have hkernel :
      ∀ᵐ left ∂muLeft, ∀ᵐ retained ∂muOff,
        kappa (left, retained) = nu (left, retained) := by
    simpa [muLeft, muOff, kappa, nu] using
      (Measure.ae_ae_of_ae_prod
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
          H N hN beta hbeta target))
  have hIterated :
      (∫⁻ left, ∫⁻ retained,
        mass (left, retained) *
          evariance (section left retained) (Measure.map eval (nu (left, retained)))
        ∂muOff ∂muLeft) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
    change (∫⁻ left, ∫⁻ retained,
      mass (left, retained) *
        evariance (section left retained) (Measure.map eval (nu (left, retained)))
      ∂muOff ∂muLeft) =
      (∫⁻ left, ∫⁻ retained,
        mass (left, retained) *
          evariance (fun targetCfg => section left retained (eval targetCfg))
            (kappa (left, retained))
      ∂muOff ∂muLeft)
    apply lintegral_congr_ae
    filter_upwards [hkernel] with left hleft
    apply lintegral_congr_ae
    filter_upwards [hleft] with retained hκ
    rw [hκ]
    exact congrArg (fun v : ENNReal => mass (left, retained) * v)
      (p4Q2AY_evariance_map_measurableEquiv
        (nu (left, retained)) eval (section left retained)
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
          H N target F hF left retained).measurable)
  have hTonelli :
      p4Q2AZ_originalJointIntegratedConditionalEnergy H N hN beta hbeta target F ≤
        (∫⁻ left, ∫⁻ retained,
          mass (left, retained) *
            evariance (section left retained) (Measure.map eval (nu (left, retained)))
          ∂muOff ∂muLeft) := by
    change (∫⁻ ctx,
      mass ctx * evariance (section ctx.1 ctx.2) (Measure.map eval (nu ctx))
      ∂muLeft.prod muOff) ≤
      (∫⁻ left, ∫⁻ retained,
        mass (left, retained) *
          evariance (section left retained) (Measure.map eval (nu (left, retained)))
        ∂muOff ∂muLeft)
    exact lintegral_prod_le
      (μ := muLeft) (ν := muOff)
      (fun ctx => mass ctx *
        evariance (section ctx.1 ctx.2) (Measure.map eval (nu ctx)))
  exact hTonelli.trans_eq hIterated

/-- Actual Wilson joint-L2 projection-defect estimate for EVERY bounded
strongly measurable concrete joint observable, at every nonnegative beta. -/
theorem p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target F ≤
      ENNReal.ofReal
        (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  calc
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target F ≤
      p4Q2AZ_originalJointIntegratedConditionalEnergy H N hN beta hbeta target F :=
      p4Q2AZ_originalJointIntegratedConditionalEnergy_ge_Haar
        H N hN beta hbeta target F hF bound hbound
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F :=
      p4Q2AZ_originalJointIntegratedConditionalEnergy_le_canonicalVariance
        H N hN beta hbeta target F hF
    _ = ENNReal.ofReal
        (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
      simpa only [p4Q2AZ_originalJointL2] using
        (GroundStateCanonicalMean.canonicalVariance_eq_condExpResidualNormSq
          H N hN beta hbeta target F hF bound hbound)

/-- AZ: One selected genuine right target link in EACH of the six colors
contributes its ACTUAL mass-weighted original Wilson Haar reference energy.
The physical six-color residual controls the sum, with NO link independence
and NO spatial-volume loss in any LOCAL Wilson comparison coefficient. -/
theorem p4Q2AZ_sixSelectedOriginalWilsonHaarEnergies_le_sixSpatialColorResiduals
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (targets : Fin 6 → PeriodicHypercubicEvenSpatialSliceLink H)
    (hColors : ∀ c : Fin 6,
      periodicHypercubicEvenSpatialSliceLinkColor H (targets c) =
        periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ c : Fin 6,
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta (targets c) F) ≤
      (∑ c : Fin 6, ENNReal.ofReal
        (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
            H N hN beta hbeta c
            (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2)) := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  apply Finset.sum_le_sum
  intro c _hc
  have hLocal :=
    p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
      H N hN beta hbeta (targets c) F hF bound hbound
  have hColor :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_sq_le_color
      H N hN beta hbeta (targets c) f
  rw [hColors c] at hColor
  have hBlock : ENNReal.ofReal
      (‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta (targets c) f‖ ^ 2) ≤
      ENNReal.ofReal
      (‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
          H N hN beta hbeta c f‖ ^ 2) := by
    exact ENNReal.ofReal_le_ofReal (by
      simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2]
        using hColor)
  exact hLocal.trans hBlock

/-- Normalized six-color version. The factor 1/6 is independent of spatial
volume; it is NOT a lower bound on the full physical six-color frame. -/
theorem p4Q2AZ_normalizedSixSelectedOriginalWilsonHaarEnergies_le_colorResiduals
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (targets : Fin 6 → PeriodicHypercubicEvenSpatialSliceLink H)
    (hColors : ∀ c : Fin 6,
      periodicHypercubicEvenSpatialSliceLinkColor H (targets c) =
        periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ((6 : ENNReal)⁻¹ *
      ∑ c : Fin 6,
        p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta (targets c) F) ≤
      ((6 : ENNReal)⁻¹ *
      ∑ c : Fin 6, ENNReal.ofReal
        (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
            H N hN beta hbeta c
            (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2)) := by
  exact mul_le_mul_left
    (p4Q2AZ_sixSelectedOriginalWilsonHaarEnergies_le_sixSpatialColorResiduals
      H N hN beta hbeta targets hColors F hF bound hbound)
    (6 : ENNReal)⁻¹

end
end MathlibAnalytic
end MGAP4D
