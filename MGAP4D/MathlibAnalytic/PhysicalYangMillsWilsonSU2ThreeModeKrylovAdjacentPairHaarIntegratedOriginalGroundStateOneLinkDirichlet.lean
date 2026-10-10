import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiberATPosteriorAEVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitProductFiberMass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-AX: integrated one-link Wilson physical ground-state Dirichlet energy

AW proved for Haar-almost every (left boundary, off-target right boundary)
that the ORIGINAL normalized physical ground-state target-link fiber
agrees with the AT genuine raw-one-slab-Wilson/continuous-physical-vacuum
Doob posterior on the actual SU(N) link. Its extended conditional variance
has a local lower factor exp(-32 beta) compared to the exact SU(N) Haar law.

Here we weight both sides by the ORIGINAL positive finite ground-state
split-target fiber MASS, then integrate on the genuine left-Haar ×
off-target-Haar outer carrier. The local factor stays exp(-32 beta), with
no number-of-spatial-plaquettes penalty.

The theorem is an integrated local conditional variance / one-link
Dirichlet form for genuine ground-state Wilson physical FIBERS. It is NOT
a full-volume transfer-operator mass gap and it does not establish
a global uniform physical Dirichlet inequality. A subsequent theorem
can connect this weighted integral to the existing exact Markov
disintegration of the whole original joint measure.

The original ground-state fiber law is kept fixed; the auxiliary
one-link completion is only a representative of off-target coordinates
used to instantiate AW's all-completions almost-everywhere theorem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open ProbabilityTheory
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4AXGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AXCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AXSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AXMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AXBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AXLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AXTargetLinks (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- Multiply an a.e. pointwise conditional variance inequality by an
ARBITRARY nonnegative outer marginal mass and integrate in ENNReal.
No cancellation/division with an exceptional mass is performed. -/
theorem p4Q2AX_massWeightedLIntegral_mono_of_ae
    {C : Type*} [MeasurableSpace C]
    (mu : Measure C)
    (mass reference physical : C → ENNReal)
    (c : ENNReal)
    (h : ∀ᵐ ctx ∂mu, c * reference ctx ≤ physical ctx) :
    (∫⁻ ctx, mass ctx * (c * reference ctx) ∂mu) ≤
      ∫⁻ ctx, mass ctx * physical ctx ∂mu := by
  apply lintegral_mono_ae
  filter_upwards [h] with ctx hctx
  exact mul_le_mul_right hctx (mass ctx)

/-- Bounded continuous SU(N) link probes are in L² under ANY genuinely
finite one-link probability law, not merely under reference Haar. -/
theorem p4Q2AX_boundedContinuous_memLp_probability
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (nu : Measure G) [IsProbabilityMeasure nu]
    (X : BoundedContinuousFunction G ℝ) :
    MemLp (fun g => X g) 2 nu := by
  exact MemLp.of_bound X.continuous.aestronglyMeasurable ‖X‖
    (Filter.Eventually.of_forall fun g => X.norm_coe_le_norm g)

/-- Choose the identity element at the target link and retain ALL
off-target coordinates exactly. This is an actual right spatial-boundary
configuration, not a change of physical Wilson or posterior measures. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  fun e => if he : e = target then 1 else retained ⟨e, he⟩

/-- The canonical completion has precisely the ORIGINAL off-target data,
including for every retained spatial link in the Wilson lattice. -/
theorem periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion_offTarget
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSliceOffTargetRestriction target
      (periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion
        H N target retained) = retained := by
  funext e
  simp [periodicHypercubicEvenSpatialSliceOffTargetRestriction,
    periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion,
    e.property]

/-- The original ground-state right-target fiber mass, computed as the
literal integral of the ORIGINAL physical Wilson joint density on the
actual singleton target SU(N) Haar carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (ctx : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) : ENNReal :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
    H N hN beta hbeta ctx.1 target ctx.2

/-- The genuine physical one-link conditional Dirichlet/variance energy,
integrated with the EXACT original ground-state fiber mass across
left-boundary Haar and retained right off-target Haar. The normalized
original fiber is evaluated through the canonical SU(N) singleton
evaluation map, not a proxy random variable or synthetic posterior. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) : ENNReal :=
  let muOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  ∫⁻ ctx,
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
      H N hN beta hbeta target ctx *
    evariance (fun g => X g)
      (Measure.map eval
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2))
      ∂muOuter

/-- Haar comparison energy with the SAME exact original physical
outer mass and the SAME target SU(N) link observable. This is the
correct reference for a mass-weighted one-link Dirichlet estimate. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedHaarReferenceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) : ENNReal :=
  let muOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  let muLink := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  ∫⁻ ctx,
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
      H N hN beta hbeta target ctx *
    (ENNReal.ofReal (Real.exp (-32 * beta)) *
       evariance (fun g => X g) muLink)
    ∂muOuter

/-- AX: the integral of the ORIGINAL physical ground-state one-link
conditional energy is bounded below by the EXACT mass-weighted Haar
reference energy, with genuine Wilson coefficient exp(-32 beta)
independent of spatial volume.

Every exceptional context from the old arbitrary L² representative is
retained inside AW's almost-everywhere quantifier and removed only under
the actual outer product-Haar integration. No global uniform time-transfer
gap or lattice-spacing rate is claimed. -/
theorem periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy_ge_Haar
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : BoundedContinuousFunction
      (Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedHaarReferenceEnergy
        H N hN beta hbeta target X ≤
      periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkIntegratedConditionalEnergy
        H N hN beta hbeta target X := by
  let muOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  let muLink := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let mass := periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
    H N hN beta hbeta target
  let phys := fun ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    evariance (fun g => X g)
      (Measure.map eval
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2))
  let refEnergy := fun _ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    evariance (fun g => X g) muLink
  let c := ENNReal.ofReal (Real.exp (-32 * beta))
  have hHaar : MemLp (fun g => X g) 2 muLink := by
    letI : IsProbabilityMeasure muLink := by dsimp [muLink]; infer_instance
    exact p4Q2AX_boundedContinuous_memLp_probability muLink X
  have hAW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalGroundStateSplitTargetFiber_ae_evariance_ge_Haar
      H N hN beta hbeta target
  have hPoint : ∀ᵐ ctx ∂muOuter, c * refEnergy ctx ≤ phys ctx := by
    filter_upwards [hAW] with ctx hctx
    let right := periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion
      H N target ctx.2
    have hOff :
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = ctx.2 :=
      periodicHypercubicEvenSpecialUnitaryRightOffTargetIdentityCompletion_offTarget
        H N target ctx.2
    let muRaw := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
      H N beta ctx.1 right target
    letI : IsProbabilityMeasure muRaw :=
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_probability
        H N beta ctx.1 right target
    have hRaw : MemLp (fun g => X g) 2 muRaw :=
      p4Q2AX_boundedContinuous_memLp_probability muRaw X
    exact hctx right hOff (fun g => X g) hHaar hRaw
  change
    (∫⁻ ctx, mass ctx * (c * refEnergy ctx) ∂muOuter) ≤
    ∫⁻ ctx, mass ctx * phys ctx ∂muOuter
  exact p4Q2AX_massWeightedLIntegral_mono_of_ae
    muOuter mass refEnergy phys c hPoint

end
end MathlibAnalytic
end MGAP4D
