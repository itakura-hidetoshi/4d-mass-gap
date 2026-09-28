import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiAEIntersectionTransport
import Mathlib.Tactic

/-!
# Finite pair-Haar support intersections

The existing pair-Haar/Fubini API proves exact AE-measurability descent for
two coordinate supports and, separately, for the special six-color family.

This file packages the same two-support theorem into an arbitrary finite-list
receiver.  It is useful when the finite family is indexed by a lattice color
class whose cardinality depends on the finite volume.

No general exchange of completed sigma-algebra intersections is asserted:
the proof literally iterates the already-established two-support Fubini
descent.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Starting from one retained support and a finite list of further supports,
AE strong measurability descends to their literal finite intersection. -/
theorem
    aestronglyMeasurable_piRestriction_iInter_list_aux_of_measurePreserving_equiv
    {Ω ι K C : Type*}
    [MeasurableSpace Ω]
    [Fintype ι]
    [MeasurableSpace K]
    (ω : Measure Ω)
    (η : Measure K)
    [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (ι → K))
    (he : MeasurePreserving e ω (Measure.pi (fun _ : ι => η)))
    (p0 : ι → Prop)
    (p : C → ι → Prop)
    (cs : List C)
    (f : Ω → ℝ)
    (h0 : AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K) p0) ∘ e)
        (inferInstance : MeasurableSpace ({i : ι // p0 i} → K))]
      f ω)
    (h : ∀ c ∈ cs,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K) (p c)) ∘ e)
          (inferInstance : MeasurableSpace ({i : ι // p c i} → K))]
        f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K)
          (fun i => p0 i ∧ ∀ c ∈ cs, p c i)) ∘ e)
        (inferInstance :
          MeasurableSpace ({i : ι // p0 i ∧ ∀ c ∈ cs, p c i} → K))]
      f ω := by
  classical
  induction cs generalizing p0 with
  | nil =>
      simpa using h0
  | cons c cs ih =>
      have hc :
          AEStronglyMeasurable[
            MeasurableSpace.comap
              ((pairHaarPiRestriction (K := K) (p c)) ∘ e)
              (inferInstance : MeasurableSpace ({i : ι // p c i} → K))]
            f ω :=
        h c (by simp)
      have h01 :=
        aestronglyMeasurable_piRestriction_and_of_measurePreserving_equiv
          ω η e he p0 (p c) f h0 hc
      have htail : ∀ d ∈ cs,
          AEStronglyMeasurable[
            MeasurableSpace.comap
              ((pairHaarPiRestriction (K := K) (p d)) ∘ e)
              (inferInstance : MeasurableSpace ({i : ι // p d i} → K))]
            f ω := by
        intro d hd
        exact h d (by simp [hd])
      have hrec :=
        ih (fun i => p0 i ∧ p c i) h01 htail
      have hpred :
          (fun i => (p0 i ∧ p c i) ∧ ∀ d ∈ cs, p d i) =
            (fun i => p0 i ∧ ∀ d ∈ c :: cs, p d i) := by
        funext i
        apply propext
        constructor
        · rintro ⟨⟨hp0, hpc⟩, hrest⟩
          refine ⟨hp0, ?_⟩
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hpc
          · exact hrest d hd
        · rintro ⟨hp0, hall⟩
          refine ⟨⟨hp0, hall c (by simp)⟩, ?_⟩
          intro d hd
          exact hall d (by simp [hd])
      rw [hpred] at hrec
      exact hrec

/-- A nonempty finite list of retained coordinate supports descends to the
literal intersection of all supports occurring in the list. -/
theorem
    aestronglyMeasurable_piRestriction_iInter_list_of_measurePreserving_equiv
    {Ω ι K C : Type*}
    [MeasurableSpace Ω]
    [Fintype ι]
    [MeasurableSpace K]
    (ω : Measure Ω)
    (η : Measure K)
    [IsProbabilityMeasure η]
    (e : Ω ≃ᵐ (ι → K))
    (he : MeasurePreserving e ω (Measure.pi (fun _ : ι => η)))
    (p : C → ι → Prop)
    (cs : List C)
    (hcs : cs ≠ [])
    (f : Ω → ℝ)
    (h : ∀ c ∈ cs,
      AEStronglyMeasurable[
        MeasurableSpace.comap
          ((pairHaarPiRestriction (K := K) (p c)) ∘ e)
          (inferInstance : MeasurableSpace ({i : ι // p c i} → K))]
        f ω) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := K)
          (fun i => ∀ c ∈ cs, p c i)) ∘ e)
        (inferInstance :
          MeasurableSpace ({i : ι // ∀ c ∈ cs, p c i} → K))]
      f ω := by
  classical
  cases cs with
  | nil =>
      contradiction
  | cons c cs =>
      have h0 :
          AEStronglyMeasurable[
            MeasurableSpace.comap
              ((pairHaarPiRestriction (K := K) (p c)) ∘ e)
              (inferInstance : MeasurableSpace ({i : ι // p c i} → K))]
            f ω :=
        h c (by simp)
      have htail : ∀ d ∈ cs,
          AEStronglyMeasurable[
            MeasurableSpace.comap
              ((pairHaarPiRestriction (K := K) (p d)) ∘ e)
              (inferInstance : MeasurableSpace ({i : ι // p d i} → K))]
            f ω := by
        intro d hd
        exact h d (by simp [hd])
      have hinter :=
        aestronglyMeasurable_piRestriction_iInter_list_aux_of_measurePreserving_equiv
          ω η e he (p c) p cs f h0 htail
      have hpred :
          (fun i => p c i ∧ ∀ d ∈ cs, p d i) =
            (fun i => ∀ d ∈ c :: cs, p d i) := by
        funext i
        apply propext
        constructor
        · rintro ⟨hc, hrest⟩ d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hc
          · exact hrest d hd
        · intro hall
          exact ⟨hall c (by simp), fun d hd => hall d (by simp [hd])⟩
      rw [hpred] at hinter
      exact hinter

end

end MGAP4D.MathlibAnalytic
