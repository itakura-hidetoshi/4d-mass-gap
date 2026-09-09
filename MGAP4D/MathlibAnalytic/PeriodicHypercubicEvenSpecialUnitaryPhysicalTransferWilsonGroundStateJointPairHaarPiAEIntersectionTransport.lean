import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiAEIntersection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Transport the finite-product support-intersection theorem across an exact
measure-preserving measurable equivalence.  The source sigma-algebras are the
pullbacks of the literal coordinate restrictions after reindexing. -/
theorem aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
    {Ω ι K : Type*}
    [MeasurableSpace Ω]
    [Fintype ι]
    [MeasurableSpace K]
    (ω : Measure Ω)
    (η : Measure K)
    [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (ι → K))
    (he : MeasurePreserving e ω (Measure.pi (fun _ : ι => η)))
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q]
    (f : Ω → ℝ)
    (hp : AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) p) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // p i} → K))]
      f ω)
    (hq : AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) q) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K))]
      f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) (fun i => p i ∧ q i)) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // p i ∧ q i} → K))]
      f ω := by
  let τ : Measure (ι → K) := Measure.pi (fun _ : ι => η)
  let f' : (ι → K) → ℝ := fun y => f (e.symm y)
  have he_symm : MeasurePreserving e.symm τ ω :=
    MeasurePreserving.symm e he

  have hpmk := hp.stronglyMeasurable_mk
  obtain ⟨P, hP, hPfac⟩ := hpmk.exists_eq_measurable_comp
  have hp' : AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) p)
        (inferInstance : MeasurableSpace ({i : ι // p i} → K))]
      f' τ := by
    refine ⟨fun y => P (pairHaarPiRestriction (K := K) p y), ?_, ?_⟩
    · exact hP.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · have h := he_symm.quasiMeasurePreserving.ae hp.ae_eq_mk
      simpa [f', hPfac, τ, Function.comp_def] using h

  have hqmk := hq.stronglyMeasurable_mk
  obtain ⟨Q, hQ, hQfac⟩ := hqmk.exists_eq_measurable_comp
  have hq' : AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) q)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K))]
      f' τ := by
    refine ⟨fun y => Q (pairHaarPiRestriction (K := K) q y), ?_, ?_⟩
    · exact hQ.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · have h := he_symm.quasiMeasurePreserving.ae hq.ae_eq_mk
      simpa [f', hQfac, τ, Function.comp_def] using h

  have hand' :=
    aestronglyMeasurable_piRestriction_and η p q f' hp' hq'
  have handmk := hand'.stronglyMeasurable_mk
  obtain ⟨A, hA, hAfac⟩ := handmk.exists_eq_measurable_comp
  refine ⟨fun x =>
      A (pairHaarPiRestriction (K := K) (fun i => p i ∧ q i) (e x)), ?_, ?_⟩
  · exact hA.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · have h := he.quasiMeasurePreserving.ae hand'.ae_eq_mk
    simpa [f', hAfac, τ, Function.comp_def] using h

end

end MathlibAnalytic
end MGAP4D
