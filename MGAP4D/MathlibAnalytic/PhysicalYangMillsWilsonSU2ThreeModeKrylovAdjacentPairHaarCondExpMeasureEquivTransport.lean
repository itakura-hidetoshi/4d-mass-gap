import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalOffLinkSingleHaarSplit
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-CZ: true Hilbert-L² conditional expectation under a Haar product equivalence

CV proved that the first-factor L² conditional expectation of a bounded
representative in a genuine product probability is the Haar fiber mean.
CY proved that the ORIGINAL physical left/right joint pair-Haar probability
is measure-isomorphic to genuine retained-link Pi Haar × one SU(N) Haar.

This file transports the Fubini + L² uniqueness argument of CV across
ANY measure-preserving measurable equivalence, then applies that result
to the exact physical CY presentation and the actual CR Hilbert projection.

The coarser sigma algebra is a NAMED DEFINITION rather than an ambient
local MeasurableSpace let binding. All ambient strong measurability,
integrability and set integrals use the original full sigma algebra.

This file does NOT conflate the independent pair-Haar reference with
interacting positive-beta Wilson conditional laws. No mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 850000

/-- The pullback of the retained first-coordinate sigma algebra under
a genuine measurable product equivalence.  Never set this as a local
ambient MeasurableSpace instance: CV's original Lean issue. -/
private abbrev p4Q2CZ_firstFactorPullback
    {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (e : Ω ≃ᵐ (α × β)) : MeasurableSpace Ω :=
  MeasurableSpace.comap (Prod.fst ∘ e)
    (inferInstance : MeasurableSpace α)

/-- Physical-measure-invariant CV theorem.  A bounded strongly measurable
real representative F of an ACTUAL L² class f has conditional expectation
onto the retained first-factor sigma algebra equal almost everywhere to
the true fiber integral.  Proved by all retained-set integrals and the
pinned mathlib Hilbert-L² uniqueness theorem; no unproved projection
naturality is assumed. -/
theorem p4Q2CZ_condExpL2_measurePreservingEquiv_fiberMean
    {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure α) (η : Measure β)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (α × β))
    (he : MeasurePreserving e μ (ν.prod η))
    (f : Lp ℝ 2 μ)
    (F : Ω → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ ω, ‖F ω‖ ≤ M)
    (hEq : F =ᵐ[μ] (f : Ω → ℝ)) :
    (condExpL2 ℝ ℝ ((measurable_fst.comp e.measurable).comap_le) f :
      Lp ℝ 2 μ) =ᵐ[μ]
      (fun ω : Ω => ∫ b : β, F (e.symm ((e ω).1, b)) ∂η) := by
  classical
  have hm : p4Q2CZ_firstFactorPullback e ≤
      (inferInstance : MeasurableSpace Ω) := by
    change MeasurableSpace.comap (Prod.fst ∘ e)
      (inferInstance : MeasurableSpace α) ≤
        (inferInstance : MeasurableSpace Ω)
    exact (measurable_fst.comp e.measurable).comap_le
  let F' : α × β → ℝ := fun p => F (e.symm p)
  have hFsm : StronglyMeasurable F' :=
    hF.comp_measurable e.symm.measurable
  have hFB : ∀ p : α × β, ‖F' p‖ ≤ M := fun p => hM (e.symm p)
  let h : α → ℝ := fun a => ∫ b : β, F' (a, b) ∂η
  have hhsm : StronglyMeasurable h := hFsm.integral_prod_right'
  have hBound : ∀ a : α, ‖h a‖ ≤ M := by
    intro a
    have hsecSm : StronglyMeasurable (fun b : β => F' (a, b)) :=
      hFsm.comp_measurable (measurable_const.prodMk measurable_id)
    have hsecInt : Integrable (fun b : β => F' (a, b)) η :=
      Integrable.of_bound hsecSm.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun b => hFB (a, b))
    calc
      ‖h a‖ = ‖∫ b : β, F' (a, b) ∂η‖ := rfl
      _ ≤ ∫ b : β, ‖F' (a, b)‖ ∂η := norm_integral_le_integral_norm _
      _ ≤ ∫ _b : β, M ∂η :=
        integral_mono_ae hsecInt.norm (integrable_const M)
          (Filter.Eventually.of_forall fun b => hFB (a, b))
      _ = M := by simp
  let g : Ω → ℝ := fun ω => h ((e ω).1)
  have hgsm : StronglyMeasurable g :=
    hhsm.comp_measurable (measurable_fst.comp e.measurable)
  have hMeanLp : MemLp g 2 μ :=
    MemLp.of_bound hgsm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => hBound ((e ω).1))
  let gLp : Lp ℝ 2 μ := hMeanLp.toLp g
  have hsmall : AEStronglyMeasurable[p4Q2CZ_firstFactorPullback e]
      (gLp : Ω → ℝ) μ := by
    have hgsmall : StronglyMeasurable[p4Q2CZ_firstFactorPullback e] g := by
      exact hhsm.comp_measurable (comap_measurable (Prod.fst ∘ e))
    exact hgsmall.aestronglyMeasurable.congr hMeanLp.coeFn_toLp.symm
  have hCondSm : AEStronglyMeasurable[p4Q2CZ_firstFactorPullback e]
      (condExpL2 ℝ ℝ hm f : Ω → ℝ) μ :=
    lpMeas.aestronglyMeasurable _
  letI : IsProbabilityMeasure (ν.prod η) := by infer_instance
  have hProdMeanSm : StronglyMeasurable (fun p : α × β => h p.1) :=
    hhsm.comp_measurable measurable_fst
  have hProdMeanInt : Integrable (fun p : α × β => h p.1) (ν.prod η) :=
    Integrable.of_bound hProdMeanSm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun p => hBound p.1)
  have hProdFInt : Integrable F' (ν.prod η) :=
    Integrable.of_bound hFsm.aestronglyMeasurable M
      (Filter.Eventually.of_forall hFB)
  have hSet : ∀ s : Set Ω,
      MeasurableSet[p4Q2CZ_firstFactorPullback e] s →
      ∫ ω in s, (gLp : Lp ℝ 2 μ) ω ∂μ =
        ∫ ω in s, (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ) ω ∂μ := by
    intro s hs
    obtain ⟨t, ht, heq⟩ :=
      (MeasurableSpace.measurableSet_comap.mp hs)
    have hset : s = e ⁻¹' (t ×ˢ Set.univ) := by
      rw [← heq]
      ext ω
      simp [Function.comp_def]
    have hprodset : MeasurableSet (t ×ˢ Set.univ : Set (α × β)) :=
      ht.prod MeasurableSet.univ
    calc
      (∫ ω in s, (gLp : Lp ℝ 2 μ) ω ∂μ) =
          ∫ ω in s, g ω ∂μ :=
        setIntegral_congr_ae (hm s hs)
          (hMeanLp.coeFn_toLp.mono fun ω hw _ => hw)
      _ = ∫ p in t ×ˢ Set.univ, h p.1 ∂(ν.prod η) := by
        rw [hset]
        simpa [g] using
          (he.setIntegral_preimage_emb e.measurableEmbedding
            (fun p : α × β => h p.1) (t ×ˢ Set.univ))
      _ = ∫ a in t, ∫ b in Set.univ, h a ∂η ∂ν :=
        setIntegral_prod (fun p : α × β => h p.1) hProdMeanInt.integrableOn
      _ = ∫ a in t, h a ∂ν := by simp
      _ = ∫ a in t, ∫ b in Set.univ, F' (a, b) ∂η ∂ν := by
        simp only [setIntegral_univ]
        rfl
      _ = ∫ p in t ×ˢ Set.univ, F' p ∂(ν.prod η) :=
        (setIntegral_prod F' hProdFInt.integrableOn).symm
      _ = ∫ ω in s, F ω ∂μ := by
        rw [hset]
        simpa [F'] using
          (he.setIntegral_preimage_emb e.measurableEmbedding
            F' (t ×ˢ Set.univ)).symm
      _ = ∫ ω in s, f ω ∂μ :=
        setIntegral_congr_ae (hm s hs)
          (hEq.mono fun ω hw _ => hw)
      _ = ∫ ω in s, (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ) ω ∂μ :=
        (integral_condExpL2_eq hm f hs (measure_ne_top _ _)).symm
  have hAE : gLp =ᵐ[μ] (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ) := by
    apply Lp.ae_eq_of_forall_setIntegral_eq' ℝ hm
      gLp (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ)
      two_ne_zero ENNReal.coe_ne_top
    · intro s hs hfin
      exact integrableOn_Lp_of_measure_ne_top gLp
        fact_one_le_two_ennreal.elim hfin.ne
    · intro s hs hfin
      exact integrableOn_Lp_of_measure_ne_top
        (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ)
        fact_one_le_two_ennreal.elim hfin.ne
    · intro s hs hfin
      exact hSet s hs
    · exact hsmall
    · exact hCondSm
  exact hAE.symm.trans hMeanLp.coeFn_toLp

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

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muH" => normalizedCompactHaar G
local notation "JH" => Lp ℝ 2 muPair

/-- The actual CR L² projection equals the genuine Haar-fiber average
under the CY measure-preserving original spatial product split,
for every globally bounded strongly measurable representative F.
In particular this is NOT an assumed commutation theorem. -/
theorem p4Q2CZ_actualPairHaarProjection_ae_eq_splitFiberMean
    (i : I) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    ((p4Q2CR_actualPairHaarCoordinateProjection H N i f : JH) :
      Joint → ℝ) =ᵐ[muPair]
      (fun z : Joint => ∫ u : G,
        F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm
          (((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i) z).1, u))
        ∂muH) := by
  classical
  let e := p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i
  have hprob : IsProbabilityMeasure muPair := by infer_instance
  letI : IsProbabilityMeasure muPair := hprob
  have hTransport :=
    p4Q2CZ_condExpL2_measurePreservingEquiv_fiberMean
      muPair (Measure.pi (fun _ : {j : I // j ≠ i} => muH)) muH
      e (p4Q2CY_actualPairHaarOffLinkSingleHaar_measurePreserving H N i)
      f F hF M hM hEq
  have hSigma :
      p4Q2CZ_firstFactorPullback e =
        p4Q2CR_actualPairHaarOffCoordinateSigma H N i := by
    exact (p4Q2CY_actualPairHaarOffCoordinateSigma_eq_splitFirst H N i).symm
  have hProj :
      (p4Q2CR_actualPairHaarCoordinateProjection H N i f : JH) =
        (condExpL2 ℝ ℝ
          (p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i) f : JH) := by
    rfl
  simpa only [hSigma, ← hProj, e] using hTransport

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
