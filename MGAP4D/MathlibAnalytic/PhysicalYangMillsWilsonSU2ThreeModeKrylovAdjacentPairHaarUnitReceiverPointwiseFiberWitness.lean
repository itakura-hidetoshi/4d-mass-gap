import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverRetainedCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarRightLinkRetainedAEDescent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasureEquivalence
import Mathlib.Tactic

/-!
# P4-Q2-H: genuine constant-unit receiver, from retained a.e. to a pointwise fiber witness

The authentic physical joint receiver is a bounded continuous function.
For the ORIGINAL Wilson joint measure (not a surrogate) every retained-right-link
a.e. representative descends to literal pointwise constancy on each target
fiber, using the reverse absolute continuity to pair Haar and the existing
full-support right-link split of P4-F2.

Consequently a single pair of actual physical configurations, differing at
only the explicit right spatial link, on which the TRUE normalized-transfer
constant-unit receiver takes different values proves strictly positive
E_unit. This is the finite pointwise witness interface for the next
positive-beta transfer/crossing calculation.

It deliberately does not claim that the already proved non-retention of
the vacuum inverse square root supplies such a unit-receiver witness.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4Q2FiberTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2FiberCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2FiberSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2FiberMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2FiberBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2FiberGroupHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2FiberSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2FiberTargetLinkFintype
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H e) :=
  Subtype.fintype (fun i : PeriodicHypercubicEvenSpatialSliceLink H => i = e)

namespace GroundStatePosteriorJoint

/-- The full-support Haar split descends retained measurability under the
ACTUAL Wilson joint law to pointwise invariance of any bounded continuous
joint observable along the indicated original right-target fiber.
No use of a quotient representative at exceptional points. -/
theorem physicalJointContinuousBCF_targetFiber_const_of_retained
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) ℝ)
    (hret : AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H 2 (originalWilsonExplicitSpatialTargetLink H)]
        (fun z => F z)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H 2 (Nat.zero_lt_succ 1) beta hbeta)) :
    ∀
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (off : PeriodicHypercubicEvenSpatialSliceOffTargetLink H
        (originalWilsonExplicitSpatialTargetLink H) →
        Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (t₁ t₂ : PeriodicHypercubicEvenSpatialSliceTargetLink H
        (originalWilsonExplicitSpatialTargetLink H) →
        Matrix.specialUnitaryGroup (Fin 2) ℂ),
      F (A,
        (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (originalWilsonExplicitSpatialTargetLink H)).symm (t₁, off)) =
      F (A,
        (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (originalWilsonExplicitSpatialTargetLink H)).symm (t₂, off)) := by
  classical
  let G := Matrix.specialUnitaryGroup (Fin 2) ℂ
  let e := originalWilsonExplicitSpatialTargetLink H
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Off := PeriodicHypercubicEvenSpatialSliceOffTargetLink H e → G
  let Target := PeriodicHypercubicEvenSpatialSliceTargetLink H e → G
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (Nat.zero_lt_succ 1) beta hbeta
  let μOff : Measure Off :=
    Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H e =>
      normalizedCompactHaar G)
  let μTarget : Measure Target :=
    Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H e =>
      normalizedCompactHaar G)
  let split : X ≃ᵐ Target × Off :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := G) e
  let E : ((X × Off) × Target) ≃ᵐ (X × X) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H 2 e
  let context : X × X → X × Off :=
    fun z => (z.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction e z.2)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  haveI : Measure.IsOpenPosMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μOff := by
    dsimp [μOff]
    infer_instance
  haveI : Measure.IsOpenPosMeasure μOff := by
    dsimp [μOff]
    infer_instance
  haveI : IsProbabilityMeasure μTarget := by
    dsimp [μTarget]
    infer_instance
  haveI : Measure.IsOpenPosMeasure μTarget := by
    dsimp [μTarget]
    infer_instance
  haveI : Measure.IsOpenPosMeasure (μ.prod μOff) :=
    Measure.prod.instIsOpenPosMeasure
  have hμν : μ.prod μ ≪ ν := by
    simpa only [μ, ν, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H 2 (Nat.zero_lt_succ 1) beta hbeta)
  obtain ⟨g, hg, hfg⟩ := hret
  have hpairAE : (fun z => F z) =ᵐ[μ.prod μ] g := hμν.ae_eq hfg
  have hSigma :
      MeasurableSpace.comap context
          (inferInstance : MeasurableSpace (X × Off)) =
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H 2 e := by
    simpa [context, periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace]
      using
      (MeasurableSpace.comap_prodMk
        (Prod.fst : X × X → X)
        (fun z : X × X =>
          periodicHypercubicEvenSpatialSliceOffTargetRestriction e z.2))
  have hEm : MeasurePreserving E
      ((μ.prod μOff).prod μTarget) (μ.prod μ) := by
    simpa [E, μ, μOff, μTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H 2 e)
  have hContextE : ∀ z : (X × Off) × Target, context (E z) = z.1 := by
    intro z
    change
      (z.1.1, periodicHypercubicEvenSpatialSliceOffTargetRestriction e
        (split.symm (z.2, z.1.2))) = z.1
    have hOff :
        periodicHypercubicEvenSpatialSliceOffTargetRestriction e
          (split.symm (z.2, z.1.2)) = z.1.2 := by
      calc
        _ = (split (split.symm (z.2, z.1.2))).2 :=
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd
            e (split.symm (z.2, z.1.2))).symm
        _ = z.1.2 := by rw [split.apply_symm_apply]
    exact Prod.ext rfl hOff
  have hretContext :
      AEStronglyMeasurable[
        MeasurableSpace.comap context (inferInstance : MeasurableSpace (X × Off))]
        (fun z => F z) (μ.prod μ) := by
    refine ⟨g, ?_, hpairAE⟩
    rw [hSigma]
    exact hg
  obtain ⟨g', hg', hfact⟩ :=
    hretContext.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hFAE : (fun z => F z) =ᵐ[μ.prod μ] (fun z => g' (context z)) := by
    simpa only [hfact, Function.comp_def] using hretContext.ae_eq_mk
  have hFsplitAE :
      (fun z : (X × Off) × Target => F (E z)) =ᵐ[
          (μ.prod μOff).prod μTarget] (fun z => g' z.1) := by
    have hae := hEm.quasiMeasurePreserving.ae hFAE
    filter_upwards [hae] with z hz
    change F (E z) = g' (context (E z)) at hz
    simpa only [hContextE z] using hz
  have hFsplitRetained :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (Prod.fst : (X × Off) × Target → X × Off) inferInstance]
        (fun z => F (E z))
        ((μ.prod μOff).prod μTarget) := by
    refine ⟨(fun z => g' z.1), ?_, hFsplitAE⟩
    exact hg'.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  have hsplitSymmContinuous :
      Continuous (fun z : Target × Off => split.symm z) := by
    let home : X ≃ₜ Target × Off :=
      Homeomorph.piEquivPiSubtypeProd
        (fun i : PeriodicHypercubicEvenSpatialSliceLink H => i = e)
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => G)
    change Continuous home.symm
    exact home.symm.continuous
  have hEContinuous : Continuous (E : (X × Off) × Target → X × X) := by
    change Continuous (fun z : (X × Off) × Target =>
      (z.1.1, split.symm (z.2, z.1.2)))
    exact (continuous_fst.comp continuous_fst).prodMk
      (hsplitSymmContinuous.comp
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  have hFContinuous : Continuous (fun z : X × X => F z) := F.continuous
  have hFiberConstant :
      ∀ ctx : X × Off, ∀ t₁ t₂ : Target,
        F (E (ctx, t₁)) = F (E (ctx, t₂)) :=
    p4F2_continuous_ae_retained_fiber_const
      (μ.prod μOff) μTarget
      (fun z => F (E z)) (hFContinuous.comp hEContinuous)
      hFsplitRetained
  intro A off t₁ t₂
  have h := hFiberConstant (A, off) t₁ t₂
  simpa [E,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv_apply]
    using h

/-- A pointwise difference of the *ACTUAL* uncentered constant-unit
receiver along a single original right target link is enough to force
strictly positive original Wilson unit receiver posterior energy. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_pos_of_targetFiber_difference
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (off : PeriodicHypercubicEvenSpatialSliceOffTargetLink H
      (originalWilsonExplicitSpatialTargetLink H) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (t₁ t₂ : PeriodicHypercubicEvenSpatialSliceTargetLink H
      (originalWilsonExplicitSpatialTargetLink H) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hDifference :
      normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (Nat.zero_lt_succ 1)
        beta (le_of_lt hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
        (A, (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (originalWilsonExplicitSpatialTargetLink H)).symm (t₁, off)) ≠
      normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (Nat.zero_lt_succ 1)
        beta (le_of_lt hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
        (A, (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (originalWilsonExplicitSpatialTargetLink H)).symm (t₂, off))) :
    0 < physicalOriginalUnitReceiverFullLinkEnergy H 2 (Nat.zero_lt_succ 1)
      beta (le_of_lt hbeta) := by
  apply physicalOriginalUnitReceiverFullLinkEnergy_pos_of_not_retained
    H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta)
    (originalWilsonExplicitSpatialTargetLink H)
  intro hret
  exact hDifference
    (physicalJointContinuousBCF_targetFiber_const_of_retained
      H beta (le_of_lt hbeta)
      (normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (Nat.zero_lt_succ 1)
        beta (le_of_lt hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
      hret A off t₁ t₂)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
