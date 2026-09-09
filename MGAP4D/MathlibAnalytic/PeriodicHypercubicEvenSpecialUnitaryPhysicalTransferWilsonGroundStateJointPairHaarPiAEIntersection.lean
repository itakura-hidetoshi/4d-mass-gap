import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarPiThreeWay
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Restrict a finite coordinate configuration to a predicate-selected support. -/
def pairHaarPiRestriction
    {ι K : Type*}
    (p : ι → Prop)
    (x : ι → K) :
    {i : ι // p i} → K :=
  fun i => x i.1

/-- Recover the `p`-restriction from the common and left-only blocks. -/
def pairHaarPiLeftDecoder
    {ι K : Type*}
    (p q : ι → Prop)
    [DecidablePred q] :
    ((PairHaarPiCommonIndex p q → K) ×
      (PairHaarPiLeftOnlyIndex p q → K)) →
      ({i : ι // p i} → K) :=
  fun y i =>
    if hq : q i.1 then
      y.1 ⟨i.1, i.2, hq⟩
    else
      y.2 ⟨⟨i.1, by
        intro hpq
        exact hq hpq.2⟩, i.2⟩

/-- Recover the `q`-restriction from the common and right-only blocks. -/
def pairHaarPiRightDecoder
    {ι K : Type*}
    (p q : ι → Prop)
    [DecidablePred p] :
    ((PairHaarPiCommonIndex p q → K) ×
      (PairHaarPiRightOnlyIndex p q → K)) →
      ({i : ι // q i} → K) :=
  fun y i =>
    if hp : p i.1 then
      y.1 ⟨i.1, hp, i.2⟩
    else
      y.2 ⟨⟨i.1, by
        intro hpq
        exact hp hpq.1⟩, hp⟩

/-- The left decoder is measurable. -/
theorem measurable_pairHaarPiLeftDecoder
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred q] :
    Measurable (pairHaarPiLeftDecoder (K := K) p q) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hq : q i.1
  · simp [pairHaarPiLeftDecoder, hq]
    exact (measurable_pi_apply (⟨i.1, i.2, hq⟩ : PairHaarPiCommonIndex p q)).comp
      measurable_fst
  · simp [pairHaarPiLeftDecoder, hq]
    exact
      (measurable_pi_apply
        (⟨⟨i.1, by
          intro hpq
          exact hq hpq.2⟩, i.2⟩ : PairHaarPiLeftOnlyIndex p q)).comp measurable_snd

/-- The right decoder is measurable. -/
theorem measurable_pairHaarPiRightDecoder
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p] :
    Measurable (pairHaarPiRightDecoder (K := K) p q) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hp : p i.1
  · simp [pairHaarPiRightDecoder, hp]
    exact (measurable_pi_apply (⟨i.1, hp, i.2⟩ : PairHaarPiCommonIndex p q)).comp
      measurable_fst
  · simp [pairHaarPiRightDecoder, hp]
    exact
      (measurable_pi_apply
        (⟨⟨i.1, by
          intro hpq
          exact hp hpq.1⟩, hp⟩ : PairHaarPiRightOnlyIndex p q)).comp measurable_snd

/-- The common/left-only output of the three-way reindex recovers exactly the
original `p`-restriction. -/
theorem pairHaarPiLeftDecoder_threeWay
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q]
    (x : ι → K) :
    pairHaarPiLeftDecoder (K := K) p q
        (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1 =
      pairHaarPiRestriction p x := by
  funext i
  by_cases hq : q i.1
  · simp [pairHaarPiLeftDecoder, pairHaarPiThreeWayMeasurableEquiv,
      pairHaarPiRestriction, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, hq]
  · simp [pairHaarPiLeftDecoder, pairHaarPiThreeWayMeasurableEquiv,
      pairHaarPiRestriction, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, hq]

/-- The common/right-only output of the three-way reindex recovers exactly the
original `q`-restriction. -/
theorem pairHaarPiRightDecoder_threeWay
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q]
    (x : ι → K) :
    pairHaarPiRightDecoder (K := K) p q
        ((pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1.1,
          (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).2) =
      pairHaarPiRestriction q x := by
  funext i
  by_cases hp : p i.1
  · simp [pairHaarPiRightDecoder, pairHaarPiThreeWayMeasurableEquiv,
      pairHaarPiRestriction, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, hp]
  · simp [pairHaarPiRightDecoder, pairHaarPiThreeWayMeasurableEquiv,
      pairHaarPiRestriction, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, hp]

/-- The common block of the three-way reindex is literally restriction to
`p ∧ q`. -/
theorem pairHaarPiThreeWay_base_eq_restriction
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q] :
    (fun x : ι → K =>
        (pairHaarPiThreeWayMeasurableEquiv (K := K) p q x).1.1) =
      pairHaarPiRestriction (fun i => p i ∧ q i) := by
  funext x i
  simp [pairHaarPiThreeWayMeasurableEquiv, pairHaarPiRestriction,
    MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc]

/-- On a finite independent product probability space, a real function which
is a.e. measurable with respect to the coordinates selected by `p` and also
a.e. measurable with respect to those selected by `q` is a.e. measurable with
respect to their common coordinates `p ∧ q`.

This is a direct finite-product/Fubini consequence of the shared-base theorem;
it does not assert a general exchange law between completion and sigma-algebra
intersection. -/
theorem aestronglyMeasurable_piRestriction_and
    {ι K : Type*}
    [Fintype ι]
    [MeasurableSpace K]
    (η : Measure K)
    [IsProbabilityMeasure η]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q]
    (f : (ι → K) → ℝ)
    (hp : AEStronglyMeasurable[
      MeasurableSpace.comap (pairHaarPiRestriction (K := K) p) inferInstance]
      f (Measure.pi (fun _ : ι => η)))
    (hq : AEStronglyMeasurable[
      MeasurableSpace.comap (pairHaarPiRestriction (K := K) q) inferInstance]
      f (Measure.pi (fun _ : ι => η))) :
    AEStronglyMeasurable[
      MeasurableSpace.comap
        (pairHaarPiRestriction (K := K) (fun i => p i ∧ q i)) inferInstance]
      f (Measure.pi (fun _ : ι => η)) := by
  let e := pairHaarPiThreeWayMeasurableEquiv (K := K) p q
  let ρ := Measure.pi (fun _ : PairHaarPiCommonIndex p q => η)
  let μ := Measure.pi (fun _ : PairHaarPiLeftOnlyIndex p q => η)
  let ν := Measure.pi (fun _ : PairHaarPiRightOnlyIndex p q => η)
  have he : MeasurePreserving e (Measure.pi (fun _ : ι => η)) ((ρ.prod μ).prod ν) := by
    simpa [e, ρ, μ, ν] using
      (pairHaarPiThreeWayMeasurableEquiv_measurePreserving η p q)

  have hpmk := hp.stronglyMeasurable_mk
  obtain ⟨L, hL, hLfac⟩ := hpmk.exists_eq_measurable_comp
  have hleft : AEStronglyMeasurable[
      MeasurableSpace.comap (fun x : ι → K => (e x).1)
        (inferInstance : MeasurableSpace
          ((PairHaarPiCommonIndex p q → K) × (PairHaarPiLeftOnlyIndex p q → K)))]
      f (Measure.pi (fun _ : ι => η)) := by
    refine ⟨fun x => L (pairHaarPiLeftDecoder (K := K) p q (e x).1), ?_, ?_⟩
    · exact
        (hL.comp_measurable (measurable_pairHaarPiLeftDecoder (K := K) p q)).comp_measurable
          (measurable_iff_comap_le.mpr le_rfl)
    · have hrep := hp.ae_eq_mk
      rw [hLfac] at hrep
      simpa [Function.comp_def, e, pairHaarPiLeftDecoder_threeWay] using hrep

  have hqmk := hq.stronglyMeasurable_mk
  obtain ⟨R, hR, hRfac⟩ := hqmk.exists_eq_measurable_comp
  have hright : AEStronglyMeasurable[
      MeasurableSpace.comap
        (fun x : ι → K => ((e x).1.1, (e x).2))
        (inferInstance : MeasurableSpace
          ((PairHaarPiCommonIndex p q → K) × (PairHaarPiRightOnlyIndex p q → K)))]
      f (Measure.pi (fun _ : ι => η)) := by
    refine ⟨fun x => R (pairHaarPiRightDecoder (K := K) p q ((e x).1.1, (e x).2)), ?_, ?_⟩
    · exact
        (hR.comp_measurable (measurable_pairHaarPiRightDecoder (K := K) p q)).comp_measurable
          (measurable_iff_comap_le.mpr le_rfl)
    · have hrep := hq.ae_eq_mk
      rw [hRfac] at hrep
      simpa [Function.comp_def, e, pairHaarPiRightDecoder_threeWay] using hrep

  have hbase :=
    aestronglyMeasurable_sharedBase_of_measurePreserving_equiv
      (Measure.pi (fun _ : ι => η)) ρ μ ν e he f hleft hright
  have hmap := pairHaarPiThreeWay_base_eq_restriction (K := K) p q
  simpa [e] using (hmap ▸ hbase)

end

end MathlibAnalytic
end MGAP4D
