import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarRightLinkFiberDescent
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

/-!
# P4-F2: authentic original right-link retained sigma algebra descent

The retained context really consists of the FULL left physical spatial
boundary and EVERY right coordinate except the single original target
link.  We identify its already-defined sigma algebra with the comap
of this literal joint coordinate restriction.

The existing original-Haar measure-preserving splitting equivalence
transports a retained-representative a.e. identity into the genuine
(left × off-target) × target independent Haar coordinates. Under the
full-support finite Haar measures, continuity then forces the Wilson
continuous joint density to be constant across the selected target
fiber.  This contradicts the exact SU(2) single-link crossing witness.

Consequently, the continuous representative of the ORIGINAL physical
Wilson joint density is not a.e. retained-right-link measurable under
the ORIGINAL pair-Haar measure.  This is not a mere all-left/all-right
separability inference from four independently chosen boundaries.

Transfer to the reciprocal square-root original Wilson vacuum and the
physical joint law is kept separate. No Dobrushin or volume-uniform
claim is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4F2DescTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4F2DescCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4F2DescSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4F2DescMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4F2DescBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4F2DescSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4F2DescTargetLinkFintype
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H e) :=
  Subtype.fintype (fun i : PeriodicHypercubicEvenSpatialSliceLink H => i = e)
local instance p4F2DescGroupHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

/-- Genuine positive-beta Wilson continuous density is NOT almost everywhere
measurable under the actual one-right-link-retained sigma-algebra, even
though all left coordinates and all off-target right coordinates remain
available. -/
theorem originalWilsonContinuousPhysicalJoint_not_retained_pairHaar
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ¬ AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H 2 (originalWilsonExplicitSpatialTargetLink H)]
        (originalWilsonContinuousPhysicalJointWeight H beta (le_of_lt hbeta))
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) := by
  classical
  let G := Matrix.specialUnitaryGroup (Fin 2) ℂ
  let e := originalWilsonExplicitSpatialTargetLink H
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Off := PeriodicHypercubicEvenSpatialSliceOffTargetLink H e → G
  let Target := PeriodicHypercubicEvenSpatialSliceTargetLink H e → G
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let μOff : Measure Off :=
    Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H e =>
      normalizedCompactHaar G)
  let μTarget : Measure Target :=
    Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H e =>
      normalizedCompactHaar G)
  let W := originalWilsonContinuousPhysicalJointWeight H beta (le_of_lt hbeta)
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
  intro hret
  have hretContext :
      AEStronglyMeasurable[
        MeasurableSpace.comap context (inferInstance : MeasurableSpace (X × Off))]
        W (μ.prod μ) := by
    rw [hSigma]
    exact hret
  obtain ⟨g, hg, hgfac⟩ :=
    hretContext.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hWae :
      W =ᵐ[μ.prod μ] (fun z => g (context z)) := by
    simpa only [hgfac, Function.comp_def] using hretContext.ae_eq_mk
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
  have hWsplitAE :
      (fun z : (X × Off) × Target => W (E z)) =ᵐ[
          (μ.prod μOff).prod μTarget]
        (fun z => g z.1) := by
    have hae := hEm.quasiMeasurePreserving.ae hWae
    filter_upwards [hae] with z hz
    change W (E z) = g (context (E z)) at hz
    simpa only [hContextE z] using hz
  have hWsplitRetained :
      AEStronglyMeasurable[
        MeasurableSpace.comap
          (Prod.fst : (X × Off) × Target → X × Off) inferInstance]
        (fun z => W (E z))
        ((μ.prod μOff).prod μTarget) := by
    refine ⟨(fun z => g z.1), ?_, hWsplitAE⟩
    exact hg.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
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
  have hWContinuous : Continuous W :=
    originalWilsonContinuousPhysicalJointWeight_continuous
      H beta (le_of_lt hbeta)
  have hFiberConstant :
      ∀ ctx : X × Off, ∀ t₁ t₂ : Target,
        W (E (ctx, t₁)) = W (E (ctx, t₂)) :=
    p4F2_continuous_ae_retained_fiber_const
      (μ.prod μOff) μTarget
      (fun z => W (E z)) (hWContinuous.comp hEContinuous)
      hWsplitRetained
  apply originalWilsonContinuousPhysicalJoint_not_targetFiberConstant H beta hbeta
  intro A off t₁ t₂
  have h := hFiberConstant (A, off) t₁ t₂
  simpa [W, E,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv_apply]
    using h

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
