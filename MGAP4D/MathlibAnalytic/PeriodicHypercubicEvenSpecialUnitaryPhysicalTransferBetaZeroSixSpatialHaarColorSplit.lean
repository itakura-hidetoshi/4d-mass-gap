import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateProductHaar
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialConditionalExpectation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Beta-zero six-spatial Haar color split

At beta zero the genuine ground-state joint law is exactly pair Haar.  This
file splits the right spatial Haar field into one complete six-spatial color
block and its off-color complement.

The resulting measurable equivalence gives the exact product coordinates

  (left boundary × off-color right boundary) × selected color block

for every one of the six genuine spatial colors.  This is the measure-theoretic
input needed to identify the genuine color conditional expectations with
product-Haar block averages and then prove their beta-zero commutation.

No positive-beta commutation or Poincare estimate is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance betaZeroSixSpatialHaarColorSplitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroSixSpatialHaarColorSplitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroSixSpatialHaarColorSplitSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroSixSpatialHaarColorSplitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroSixSpatialHaarColorSplitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroSixSpatialHaarColorSplitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Spatial links belonging to one selected member of the genuine six-color
spatial decomposition. -/
abbrev PeriodicHypercubicEvenSpatialSliceColorLink
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) : Type :=
  {e : PeriodicHypercubicEvenSpatialSliceLink H //
    periodicHypercubicEvenSpatialSliceLinkColor H e = color}

local instance betaZeroSixSpatialHaarColorSplitColorLinkFintype
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    Fintype (PeriodicHypercubicEvenSpatialSliceColorLink H color) :=
  Subtype.fintype
    (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpatialSliceLinkColor H e = color)

/-- Split a complete right-boundary configuration into one selected spatial
color block and all right-boundary links outside that color. -/
noncomputable def periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge ≃ᵐ
      (PeriodicHypercubicEvenSpatialSliceColorLink H color → Gauge) ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H color → Gauge) := by
  classical
  exact
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => Gauge)
      (fun e =>
        periodicHypercubicEvenSpatialSliceLinkColor H e = color)

@[simp] theorem periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv_fst_apply
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (e : PeriodicHypercubicEvenSpatialSliceColorLink H color) :
    (periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
      (Gauge := Gauge) color right).1 e =
      right e.1 := by
  classical
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv_snd
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge) :
    (periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
      (Gauge := Gauge) color right).2 =
      periodicHypercubicEvenSpatialSliceOffColorRestriction color right := by
  classical
  rfl

/-- Spatial product Haar splits exactly into the selected color block and its
off-color complement. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceColorOffColorHaar_measurePreserving
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurePreserving
      (periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) color)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      ((Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceColorLink H color =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffColorLink H color =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  simpa [periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv] using
    (measurePreserving_piEquivPiSubtypeProd
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        periodicHypercubicEvenSpatialSliceLinkColor H e = color))

/-- Reassociate the product coordinates as
`(left × off-color) × selected-color` and reconstruct the original
`(left,right)` pair. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitMeasurableEquiv
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
      (PeriodicHypercubicEvenSpatialSliceColorLink H color →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := by
  classical
  let split :=
    periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
      (H := H) (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) color
  let assoc :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        (PeriodicHypercubicEvenSpatialSliceColorLink H color →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    MeasurableEquiv.prodAssoc
  let swapInner :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    (MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm
  let splitNested :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    (MeasurableEquiv.refl _).prodCongr split.symm
  exact (assoc.trans swapInner).trans splitNested

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitMeasurableEquiv_apply
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
      (PeriodicHypercubicEvenSpatialSliceColorLink H color →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitMeasurableEquiv
        H N color z =
      (z.1.1,
        (periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
          (H := H) (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) color).symm
            (z.2, z.1.2)) := by
  classical
  rfl

/-- Pair Haar is exactly the product of left Haar, off-color Haar, and the
selected color-block Haar in the split coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitHaar_measurePreserving
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitMeasurableEquiv
        H N color)
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffColorLink H color =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceColorLink H color =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))))
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μColor := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceColorLink H color =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffColorLink H color =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split :=
    periodicHypercubicEvenSpatialSliceColorOffColorMeasurableEquiv
      (H := H) (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) color
  let assoc :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        (PeriodicHypercubicEvenSpatialSliceColorLink H color →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    MeasurableEquiv.prodAssoc
  let swapInner :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    (MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm
  let splitNested :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffColorLink H color →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    (MeasurableEquiv.refl _).prodCongr split.symm
  have hAssoc : MeasurePreserving assoc
      ((μ.prod μOff).prod μColor)
      (μ.prod (μOff.prod μColor)) := by
    simpa [assoc] using
      (MeasureTheory.measurePreserving_prodAssoc μ μOff μColor)
  have hSwap : MeasurePreserving swapInner
      (μ.prod (μOff.prod μColor))
      (μ.prod (μColor.prod μOff)) := by
    simpa [swapInner] using
      (MeasurePreserving.id μ).prod
        (Measure.measurePreserving_swap :
          MeasurePreserving Prod.swap (μOff.prod μColor) (μColor.prod μOff))
  have hsplit : MeasurePreserving split μ (μColor.prod μOff) := by
    simpa [split, μ, μColor, μOff] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceColorOffColorHaar_measurePreserving
        H N color)
  have hSplitNested : MeasurePreserving splitNested
      (μ.prod (μColor.prod μOff))
      (μ.prod μ) := by
    simpa [splitNested] using
      (MeasurePreserving.id μ).prod hsplit.symm
  simpa [μ, μColor, μOff, split, assoc, swapInner, splitNested,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitMeasurableEquiv] using
    (hAssoc.trans hSwap).trans hSplitNested

/-- At beta zero, the genuine ground-state joint law itself is carried by the
inverse split to the literal `(left × off-color) × color-block` product Haar
law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_colorSplit_measurePreserving
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitMeasurableEquiv
        H N color).symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN 0 (by norm_num))
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffColorLink H color =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceColorLink H color =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN]
  exact
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointColorSplitHaar_measurePreserving
      H N color).symm

end

end MGAP4D.MathlibAnalytic
