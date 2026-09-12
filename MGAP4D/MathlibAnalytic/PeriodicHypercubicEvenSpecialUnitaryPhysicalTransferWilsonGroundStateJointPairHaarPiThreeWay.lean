import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarAEEquivTransport
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Coordinates common to two retained predicates. -/
abbrev PairHaarPiCommonIndex {ι : Type*} (p q : ι → Prop) :=
  {i : ι // p i ∧ q i}

/-- Coordinates outside the common support. -/
abbrev PairHaarPiRestIndex {ι : Type*} (p q : ι → Prop) :=
  {i : ι // ¬ (p i ∧ q i)}

/-- Among the non-common coordinates, those retained by the left predicate. -/
abbrev PairHaarPiLeftOnlyIndex {ι : Type*} (p q : ι → Prop) :=
  {i : PairHaarPiRestIndex p q // p i.1}

/-- Among the non-common coordinates, those not retained by the left predicate. -/
abbrev PairHaarPiRightOnlyIndex {ι : Type*} (p q : ι → Prop) :=
  {i : PairHaarPiRestIndex p q // ¬ p i.1}

/-- Exact measurable reindexing of a finite coordinate product into
`common × left-only × right-only` blocks.  No measure assertion is bundled
into the equivalence itself. -/
noncomputable def pairHaarPiThreeWayMeasurableEquiv
    {ι K : Type*}
    [MeasurableSpace K]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q] :
    (ι → K) ≃ᵐ
      (((PairHaarPiCommonIndex p q → K) ×
          (PairHaarPiLeftOnlyIndex p q → K)) ×
        (PairHaarPiRightOnlyIndex p q → K)) := by
  let e0 :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : ι => K) (fun i => p i ∧ q i)
  let e1 :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : PairHaarPiRestIndex p q => K) (fun i => p i.1)
  exact
    e0.trans
      ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (PairHaarPiCommonIndex p q → K)) e1).trans
        MeasurableEquiv.prodAssoc.symm)

/-- The three-way finite coordinate reindexing preserves the corresponding
product probability measure exactly. -/
theorem pairHaarPiThreeWayMeasurableEquiv_measurePreserving
    {ι K : Type*}
    [Fintype ι]
    [MeasurableSpace K]
    (η : Measure K)
    [IsProbabilityMeasure η]
    (p q : ι → Prop)
    [DecidablePred p]
    [DecidablePred q] :
    MeasurePreserving
      (pairHaarPiThreeWayMeasurableEquiv (K := K) p q)
      (Measure.pi (fun _ : ι => η))
      (((Measure.pi (fun _ : PairHaarPiCommonIndex p q => η)).prod
          (Measure.pi (fun _ : PairHaarPiLeftOnlyIndex p q => η))).prod
        (Measure.pi (fun _ : PairHaarPiRightOnlyIndex p q => η))) := by
  let ρ := Measure.pi (fun _ : PairHaarPiCommonIndex p q => η)
  let τ := Measure.pi (fun _ : PairHaarPiRestIndex p q => η)
  let μ := Measure.pi (fun _ : PairHaarPiLeftOnlyIndex p q => η)
  let ν := Measure.pi (fun _ : PairHaarPiRightOnlyIndex p q => η)
  have h0 :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : ι => K) (fun i => p i ∧ q i))
        (Measure.pi (fun _ : ι => η)) (ρ.prod τ) := by
    simpa [ρ, τ] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun _ : ι => η) (fun i => p i ∧ q i))
  have h1 :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : PairHaarPiRestIndex p q => K) (fun i => p i.1))
        τ (μ.prod ν) := by
    simpa [τ, μ, ν] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun _ : PairHaarPiRestIndex p q => η) (fun i => p i.1))
  have hp :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (PairHaarPiCommonIndex p q → K))
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : PairHaarPiRestIndex p q => K) (fun i => p i.1)))
        (ρ.prod τ) (ρ.prod (μ.prod ν)) := by
    exact MeasurePreserving.prod (MeasurePreserving.id ρ) h1
  have ha :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          (PairHaarPiCommonIndex p q → K) ×
              ((PairHaarPiLeftOnlyIndex p q → K) ×
                (PairHaarPiRightOnlyIndex p q → K)) ≃ᵐ
            (((PairHaarPiCommonIndex p q → K) ×
                (PairHaarPiLeftOnlyIndex p q → K)) ×
              (PairHaarPiRightOnlyIndex p q → K)))
        (ρ.prod (μ.prod ν)) ((ρ.prod μ).prod ν) := by
    exact
      MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (MeasureTheory.measurePreserving_prodAssoc ρ μ ν)
  simpa [pairHaarPiThreeWayMeasurableEquiv, ρ, μ, ν] using
    h0.trans (hp.trans ha)

end

end MathlibAnalytic
end MGAP4D
