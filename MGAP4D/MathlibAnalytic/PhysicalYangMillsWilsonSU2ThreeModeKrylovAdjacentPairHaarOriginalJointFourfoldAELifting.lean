import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointCrossingPositiveMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# P4-F1: fourfold a.e. lifting for the original physical Wilson joint density

The canonical continuous Wilson joint representative equals the ORIGINAL
L²-vacuum-based joint normalized weight pair-Haar a.e. (PR #5296).
The strict continuous crossing-minor locus has positive fourfold Haar
measure (PR #5297).

We transport the SAME pair-Haar a.e. equality simultaneously through
the four maps (A₁,A₂,B₁,B₂) ↦ (Aᵢ,Bⱼ).  The generic measure-theoretic
argument uses the actual binary product measure twice, the pinned mathlib
QuasiMeasurePreserving fst/snd projections and their prodMap theorem.
There is no illicit pointwise substitution of an L² representative.

The resulting fourfold common full-measure event transfers the strict
minor to the original physical Wilson joint weight on a positive-measure
set.  Neither retained-right-link nonmeasurability, volume-uniform
posterior energy, nor a continuum gap follows at this stage.
No Dobrushin assumption is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Four crossed projections pull a pair-law a.e. equality back to
one COMMON full-measure event on (A₁,A₂) × (B₁,B₂).
The SFinite hypotheses used by mathlib's product quasi-measure-
preservation are stated explicitly; no independence beyond the
original fourfold product law is silently postulated. -/
theorem pairHaar_ae_eq_fourfold_crossings
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {f g : α × α → ℝ} (hfg : f =ᵐ[μ.prod μ] g) :
    ∀ᵐ z ∂((μ.prod μ).prod (μ.prod μ)),
      f (z.1.1, z.2.1) = g (z.1.1, z.2.1) ∧
      f (z.1.2, z.2.2) = g (z.1.2, z.2.2) ∧
      f (z.1.1, z.2.2) = g (z.1.1, z.2.2) ∧
      f (z.1.2, z.2.1) = g (z.1.2, z.2.1) := by
  haveI : SFinite (μ.prod μ) := inferInstance
  have hfst : Measure.QuasiMeasurePreserving
      (Prod.fst : α × α → α) (μ.prod μ) μ :=
    Measure.quasiMeasurePreserving_fst
  have hsnd : Measure.QuasiMeasurePreserving
      (Prod.snd : α × α → α) (μ.prod μ) μ :=
    Measure.quasiMeasurePreserving_snd
  have h11 :
      (fun z : (α × α) × (α × α) => f (z.1.1, z.2.1)) =ᵐ[
        (μ.prod μ).prod (μ.prod μ)]
      (fun z => g (z.1.1, z.2.1)) := by
    simpa only [Function.comp_def, Prod.map] using
      (hfst.prodMap hfst).ae_eq hfg
  have h22 :
      (fun z : (α × α) × (α × α) => f (z.1.2, z.2.2)) =ᵐ[
        (μ.prod μ).prod (μ.prod μ)]
      (fun z => g (z.1.2, z.2.2)) := by
    simpa only [Function.comp_def, Prod.map] using
      (hsnd.prodMap hsnd).ae_eq hfg
  have h12 :
      (fun z : (α × α) × (α × α) => f (z.1.1, z.2.2)) =ᵐ[
        (μ.prod μ).prod (μ.prod μ)]
      (fun z => g (z.1.1, z.2.2)) := by
    simpa only [Function.comp_def, Prod.map] using
      (hfst.prodMap hsnd).ae_eq hfg
  have h21 :
      (fun z : (α × α) × (α × α) => f (z.1.2, z.2.1)) =ᵐ[
        (μ.prod μ).prod (μ.prod μ)]
      (fun z => g (z.1.2, z.2.1)) := by
    simpa only [Function.comp_def, Prod.map] using
      (hsnd.prodMap hfst).ae_eq hfg
  filter_upwards [h11, h22, h12, h21] with z hz11 hz22 hz12 hz21
  exact ⟨hz11, hz22, hz12, hz21⟩

local instance p4F1TopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4F1CompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4F1SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4F1MeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4F1BorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4F1SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4F1SpatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- The 2×2 determinant of the ORIGINAL physical L²-vacuum
normalized joint density, not of a substituted pointwise continuous
representative. -/
noncomputable def originalWilsonOriginalPhysicalJointTwoByTwoMinor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H 2 (by norm_num) beta hbeta
  W (A₁, B₁) * W (A₂, B₂) - W (A₁, B₂) * W (A₂, B₁)

/-- On one common full fourfold product-Haar measure event, all four
entries of the continuous and original normalized Wilson joint
weights agree. Each crossing projection is null-preserving. -/
theorem originalWilsonContinuousPhysicalJointWeight_fourfold_ae_eq_original
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)).prod
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))),
      originalWilsonContinuousPhysicalJointWeight H beta hbeta (z.1.1, z.2.1) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta (z.1.1, z.2.1) ∧
      originalWilsonContinuousPhysicalJointWeight H beta hbeta (z.1.2, z.2.2) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta (z.1.2, z.2.2) ∧
      originalWilsonContinuousPhysicalJointWeight H beta hbeta (z.1.1, z.2.2) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta (z.1.1, z.2.2) ∧
      originalWilsonContinuousPhysicalJointWeight H beta hbeta (z.1.2, z.2.1) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta (z.1.2, z.2.1) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  haveI hμProbability : IsProbabilityMeasure μ :=
    p4F1SpatialHaarProbability H
  haveI hμSFinite : SFinite μ := inferInstance
  have hpair :
      (originalWilsonContinuousPhysicalJointWeight H beta hbeta) =ᵐ[μ.prod μ]
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta z) := by
    simpa only [μ] using
      (originalWilsonContinuousPhysicalJointWeight_ae_eq_original H beta hbeta)
  exact pairHaar_ae_eq_fourfold_crossings μ hpair

/-- The continuous-version and ORIGINAL L²-version genuine Wilson
crossing determinants agree on a common fourfold Haar-a.e. event. -/
theorem originalWilsonContinuousPhysicalJointTwoByTwoMinor_fourfold_ae_eq_original
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)).prod
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))),
      originalWilsonContinuousPhysicalJointTwoByTwoMinor
          H beta hbeta z.1.1 z.1.2 z.2.1 z.2.2 =
        originalWilsonOriginalPhysicalJointTwoByTwoMinor
          H beta hbeta z.1.1 z.1.2 z.2.1 z.2.2 := by
  filter_upwards
    [originalWilsonContinuousPhysicalJointWeight_fourfold_ae_eq_original
      H beta hbeta] with z hz
  rcases hz with ⟨hz11, hz22, hz12, hz21⟩
  unfold originalWilsonContinuousPhysicalJointTwoByTwoMinor
    originalWilsonOriginalPhysicalJointTwoByTwoMinor
  rw [hz11, hz22, hz12, hz21]

/-- The strict minor locus of the ORIGINAL original-L²-version
normalized Wilson joint weight has strictly positive measure under
FOUR independent physical spatial Haar configurations at every
finite H and every beta>0. This is an a.e.-invariant conclusion,
not a false pointwise identification of representative values. -/
theorem originalWilsonOriginalPhysicalJointStrictMinorSet_positiveHaarMeasure
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 <
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)).prod
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))
        {z : originalWilsonFourSpatialBoundaries H |
          0 < originalWilsonOriginalPhysicalJointTwoByTwoMinor
            H beta (le_of_lt hbeta) z.1.1 z.1.2 z.2.1 z.2.2} := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let μ₄ := (μ.prod μ).prod (μ.prod μ)
  have hminor :=
    originalWilsonContinuousPhysicalJointTwoByTwoMinor_fourfold_ae_eq_original
      H beta (le_of_lt hbeta)
  have hsets :
      originalWilsonContinuousPhysicalJointStrictMinorSet
        H beta (le_of_lt hbeta) =ᵐ[μ₄]
        {z : originalWilsonFourSpatialBoundaries H |
          0 < originalWilsonOriginalPhysicalJointTwoByTwoMinor
            H beta (le_of_lt hbeta) z.1.1 z.1.2 z.2.1 z.2.2} := by
    filter_upwards [hminor] with z hz
    change (0 < originalWilsonContinuousPhysicalJointTwoByTwoMinor
      H beta (le_of_lt hbeta) z.1.1 z.1.2 z.2.1 z.2.2) ↔
      (0 < originalWilsonOriginalPhysicalJointTwoByTwoMinor
        H beta (le_of_lt hbeta) z.1.1 z.1.2 z.2.1 z.2.2)
    rw [hz]
  have hpos :
      0 < μ₄ (originalWilsonContinuousPhysicalJointStrictMinorSet
        H beta (le_of_lt hbeta)) := by
    simpa only [μ₄, μ] using
      originalWilsonContinuousPhysicalJointStrictMinorSet_positiveHaarMeasure H beta hbeta
  exact lt_of_lt_of_eq hpos (measure_congr hsets)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
