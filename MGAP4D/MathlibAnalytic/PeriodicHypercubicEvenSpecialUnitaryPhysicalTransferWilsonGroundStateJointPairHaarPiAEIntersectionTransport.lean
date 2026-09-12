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
  have hpRep :
      f =ᵐ[ω] fun x => P (pairHaarPiRestriction (K := K) p (e x)) := by
    have h := hp.ae_eq_mk
    rw [hPfac] at h
    simpa [Function.comp_def] using h
  have hp' : AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) p)
        (inferInstance : MeasurableSpace ({i : ι // p i} → K))]
      f' τ := by
    refine ⟨fun y => P (pairHaarPiRestriction (K := K) p y), ?_, ?_⟩
    · exact hP.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · have h := he_symm.quasiMeasurePreserving.ae hpRep
      simpa [f', τ, Function.comp_def] using h

  have hqmk := hq.stronglyMeasurable_mk
  obtain ⟨Q, hQ, hQfac⟩ := hqmk.exists_eq_measurable_comp
  have hqRep :
      f =ᵐ[ω] fun x => Q (pairHaarPiRestriction (K := K) q (e x)) := by
    have h := hq.ae_eq_mk
    rw [hQfac] at h
    simpa [Function.comp_def] using h
  have hq' : AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) q)
        (inferInstance : MeasurableSpace ({i : ι // q i} → K))]
      f' τ := by
    refine ⟨fun y => Q (pairHaarPiRestriction (K := K) q y), ?_, ?_⟩
    · exact hQ.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · have h := he_symm.quasiMeasurePreserving.ae hqRep
      simpa [f', τ, Function.comp_def] using h

  have hand' :=
    aestronglyMeasurable_piRestriction_and η p q f' hp' hq'
  have handmk := hand'.stronglyMeasurable_mk
  obtain ⟨A, hA, hAfac⟩ := handmk.exists_eq_measurable_comp
  have handRep :
      f' =ᵐ[τ]
        fun y => A (pairHaarPiRestriction (K := K) (fun i => p i ∧ q i) y) := by
    have h := hand'.ae_eq_mk
    rw [hAfac] at h
    simpa [Function.comp_def] using h
  refine ⟨fun x =>
      A (pairHaarPiRestriction (K := K) (fun i => p i ∧ q i) (e x)), ?_, ?_⟩
  · exact hA.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · have h := he.quasiMeasurePreserving.ae handRep
    simpa [f', τ, Function.comp_def] using h

/-- Six-fold finite support intersection across an exact measure-preserving
coordinate presentation.  This iterates the two-support Fubini theorem rather
than exchanging completion with a six-fold sigma-algebra intersection. -/
theorem aestronglyMeasurable_piRestriction_iInter_finSix_of_measurePreserving_equiv
    {Ω ι K : Type*}
    [MeasurableSpace Ω]
    [Fintype ι]
    [MeasurableSpace K]
    (ω : Measure Ω)
    (η : Measure K)
    [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (ι → K))
    (he : MeasurePreserving e ω (Measure.pi (fun _ : ι => η)))
    (p : Fin 6 → ι → Prop)
    [∀ c, DecidablePred (p c)]
    (f : Ω → ℝ)
    (h : ∀ c : Fin 6,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K) (p c)) ∘ e)
          (inferInstance : MeasurableSpace ({i : ι // p c i} → K))]
        f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) (fun i => ∀ c : Fin 6, p c i)) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // ∀ c : Fin 6, p c i} → K))]
      f ω := by
  have h01 :=
    aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
      ω η e he (p 0) (p 1) f (h 0) (h 1)
  have h012 :=
    aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
      ω η e he (fun i => p 0 i ∧ p 1 i) (p 2) f h01 (h 2)
  have h0123 :=
    aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
      ω η e he (fun i => (p 0 i ∧ p 1 i) ∧ p 2 i) (p 3) f h012 (h 3)
  have h01234 :=
    aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
      ω η e he (fun i => ((p 0 i ∧ p 1 i) ∧ p 2 i) ∧ p 3 i) (p 4) f h0123 (h 4)
  have h012345 :=
    aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
      ω η e he
        (fun i => (((p 0 i ∧ p 1 i) ∧ p 2 i) ∧ p 3 i) ∧ p 4 i)
        (p 5) f h01234 (h 5)
  have hpred :
      (fun i => ((((p 0 i ∧ p 1 i) ∧ p 2 i) ∧ p 3 i) ∧ p 4 i) ∧ p 5 i) =
        (fun i => ∀ c : Fin 6, p c i) := by
    funext i
    apply propext
    constructor
    · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ c
      fin_cases c <;> assumption
    · intro hall
      exact ⟨⟨⟨⟨⟨hall 0, hall 1⟩, hall 2⟩, hall 3⟩, hall 4⟩, hall 5⟩
  rw [hpred] at h012345
  exact h012345

end

end MathlibAnalytic
end MGAP4D
