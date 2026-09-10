import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkNormalizedFiberMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The singleton subtype carrying exactly the selected right-boundary link. -/
abbrev PeriodicHypercubicEvenSpatialSliceTargetLink
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  {e : PeriodicHypercubicEvenSpatialSliceLink H // e = target}

/-- Use the generic subtype product indexing chosen by
`measurePreserving_piEquivPiSubtypeProd`.  This local instance is mathematically
the same singleton finite type as `Fintype.subtypeEq`; fixing its presentation
prevents `Measure.pi` from depending on two definitionally different Fintype
receipts for the target subtype. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- Split a complete right-boundary configuration into the selected target
coordinate and all off-target coordinates.  The first factor is deliberately
kept as the singleton target subtype: this is exactly the presentation used by
Mathlib's product-measure splitting theorem and avoids any ad hoc reindexing. -/
noncomputable def periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge ≃ᵐ
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target → Gauge) ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge) := by
  classical
  exact
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => Gauge)
      (fun e => e = target)

/-- The target factor of the coordinate split is literal coordinate
restriction to the singleton target subtype. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_fst_apply
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (e : PeriodicHypercubicEvenSpatialSliceTargetLink H target) :
    (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv target right).1 e =
      right e.1 := by
  classical
  rfl

/-- The second factor of the coordinate split is exactly the already-canonical
off-target restriction used by the one-link conditional-expectation layer. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge) :
    (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv target right).2 =
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right := by
  classical
  rfl

/-- In particular, evaluation of the target factor at its canonical inhabitant
is exactly evaluation of the original configuration at `target`. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_target
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge) :
    (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv target right).1
        ⟨target, rfl⟩ = right target := by
  classical
  rfl

/-- Normalized product Haar measure on the complete right boundary is carried
measure-preservingly to the product of the singleton target Haar factor and
the off-target product Haar factor.  This is purely a coordinate theorem: it
uses no ground-state density, no fiber-normalization receipt, and no
conditional-probability identification. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurePreserving
      (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      ((Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  classical
  simpa [periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv] using
    (measurePreserving_piEquivPiSubtypeProd
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target))

end

end MathlibAnalytic
end MGAP4D
