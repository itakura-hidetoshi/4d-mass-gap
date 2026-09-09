import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarAEEquivTransport
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Coordinates common to two retained supports. -/
abbrev PairHaarPiCommonIndex {ι : Type*} (s t : Set ι) :=
  {i : ι // i ∈ s ∩ t}

/-- Coordinates outside the common support. -/
abbrev PairHaarPiRestIndex {ι : Type*} (s t : Set ι) :=
  {i : ι // i ∉ s ∩ t}

/-- Among the non-common coordinates, those retained by the left support. -/
abbrev PairHaarPiLeftOnlyIndex {ι : Type*} (s t : Set ι) :=
  {i : PairHaarPiRestIndex s t // i.1 ∈ s}

/-- Among the non-common coordinates, those not retained by the left support. -/
abbrev PairHaarPiRightOnlyIndex {ι : Type*} (s t : Set ι) :=
  {i : PairHaarPiRestIndex s t // i.1 ∉ s}

noncomputable instance pairHaarPiCommonIndexFintype
    {ι : Type*} [Fintype ι] (s t : Set ι) :
    Fintype (PairHaarPiCommonIndex s t) :=
  Fintype.ofFinite _

noncomputable instance pairHaarPiRestIndexFintype
    {ι : Type*} [Fintype ι] (s t : Set ι) :
    Fintype (PairHaarPiRestIndex s t) :=
  Fintype.ofFinite _

noncomputable instance pairHaarPiLeftOnlyIndexFintype
    {ι : Type*} [Fintype ι] (s t : Set ι) :
    Fintype (PairHaarPiLeftOnlyIndex s t) :=
  Fintype.ofFinite _

noncomputable instance pairHaarPiRightOnlyIndexFintype
    {ι : Type*} [Fintype ι] (s t : Set ι) :
    Fintype (PairHaarPiRightOnlyIndex s t) :=
  Fintype.ofFinite _

/-- Exact measurable reindexing of a finite coordinate product into
`common × left-only × right-only` blocks.  No measure assertion is bundled
into the equivalence itself. -/
noncomputable def pairHaarPiThreeWayMeasurableEquiv
    {ι K : Type*}
    [MeasurableSpace K]
    (s t : Set ι) :
    (ι → K) ≃ᵐ
      (((PairHaarPiCommonIndex s t → K) ×
          (PairHaarPiLeftOnlyIndex s t → K)) ×
        (PairHaarPiRightOnlyIndex s t → K)) := by
  classical
  let e0 :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : ι => K) (fun i => i ∈ s ∩ t)
  let e1 :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : PairHaarPiRestIndex s t => K) (fun i => i.1 ∈ s)
  exact
    e0.trans
      ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (PairHaarPiCommonIndex s t → K)) e1).trans
        MeasurableEquiv.prodAssoc.symm)

/-- The three-way finite coordinate reindexing preserves the corresponding
product probability measure exactly. -/
theorem pairHaarPiThreeWayMeasurableEquiv_measurePreserving
    {ι K : Type*}
    [Fintype ι]
    [MeasurableSpace K]
    (η : Measure K)
    [IsProbabilityMeasure η]
    (s t : Set ι) :
    MeasurePreserving
      (pairHaarPiThreeWayMeasurableEquiv (K := K) s t)
      (Measure.pi (fun _ : ι => η))
      (((Measure.pi (fun _ : PairHaarPiCommonIndex s t => η)).prod
          (Measure.pi (fun _ : PairHaarPiLeftOnlyIndex s t => η))).prod
        (Measure.pi (fun _ : PairHaarPiRightOnlyIndex s t => η))) := by
  classical
  let ρ := Measure.pi (fun _ : PairHaarPiCommonIndex s t => η)
  let τ := Measure.pi (fun _ : PairHaarPiRestIndex s t => η)
  let μ := Measure.pi (fun _ : PairHaarPiLeftOnlyIndex s t => η)
  let ν := Measure.pi (fun _ : PairHaarPiRightOnlyIndex s t => η)
  have h0 :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : ι => K) (fun i => i ∈ s ∩ t))
        (Measure.pi (fun _ : ι => η)) (ρ.prod τ) := by
    simpa [ρ, τ] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun _ : ι => η) (fun i => i ∈ s ∩ t))
  have h1 :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : PairHaarPiRestIndex s t => K) (fun i => i.1 ∈ s))
        τ (μ.prod ν) := by
    simpa [τ, μ, ν] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun _ : PairHaarPiRestIndex s t => η) (fun i => i.1 ∈ s))
  have hp :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (PairHaarPiCommonIndex s t → K))
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : PairHaarPiRestIndex s t => K) (fun i => i.1 ∈ s)))
        (ρ.prod τ) (ρ.prod (μ.prod ν)) := by
    exact MeasurePreserving.prod (MeasurePreserving.id ρ) h1
  have ha :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          (PairHaarPiCommonIndex s t → K) ×
              ((PairHaarPiLeftOnlyIndex s t → K) ×
                (PairHaarPiRightOnlyIndex s t → K)) ≃ᵐ
            (((PairHaarPiCommonIndex s t → K) ×
                (PairHaarPiLeftOnlyIndex s t → K)) ×
              (PairHaarPiRightOnlyIndex s t → K)))
        (ρ.prod (μ.prod ν)) ((ρ.prod μ).prod ν) := by
    exact
      MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (MeasureTheory.measurePreserving_prodAssoc ρ μ ν)
  simpa [pairHaarPiThreeWayMeasurableEquiv, ρ, μ, ν] using
    h0.trans (hp.trans ha)

end

end MathlibAnalytic
end MGAP4D
