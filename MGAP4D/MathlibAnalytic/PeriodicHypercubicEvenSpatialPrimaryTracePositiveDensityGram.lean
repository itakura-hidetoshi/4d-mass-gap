import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical
import MGAP4D.MathlibAnalytic.ContinuousInfiniteRangePowerWithDensityGram
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange
import Mathlib.Tactic

/-!
# Positive-density Gram nondegeneracy on one physical spatial slice

The H1-D5 residual after #5048 lives on a single spatial slice equipped with an
equivalent positive reweighting of product Haar.  This file supplies the
one-slice analogue of the earlier boundary positive-density trace package.

We first build a concrete section of the canonical primary-spatial plaquette
holonomy by placing an arbitrary SU(2) element on one of its four distinct
links and the identity elsewhere.  Hence the Wilson energy, and therefore the
normalized real trace, has infinite range already on the one-slice
configuration space.

The generic full-support positive-density theorem then gives finite Gram
nondegeneracy of every initial normalized-trace power family under any finite
density which is nonzero almost everywhere.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

local instance spatialTraceGramTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance spatialTraceGramCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance spatialTraceGramSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance spatialTraceGramMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance spatialTraceGramBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance spatialTraceGramSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance spatialTraceGramHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance spatialTraceGramSpatialHaarFinite (H : ℕ) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance spatialTraceGramSpatialHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The four intrinsic links of the canonical primary spatial plaquette are
pairwise distinct. -/
theorem periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge_injective
    (H : ℕ) :
    Function.Injective
      (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H) := by
  intro i j hij
  apply
    (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H).injective
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding_eq_primarySliceLink,
    periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding_eq_primarySliceLink]
  exact congrArg
    (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H) hij

/-- Concrete section of the intrinsic primary-spatial plaquette holonomy:
place `U` on edge zero and identity on every other spatial link. -/
noncomputable def periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomySection
    (H : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  fun e =>
    if e = periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 0 then
      U
    else
      1

/-- The concrete one-slice section is a right inverse of the canonical
primary-spatial plaquette holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_section
    (H : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomySection H U)
        (periodicHypercubicEvenPrimarySpatialSlicePlaquette H) =
      U := by
  have h10 :
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 1 ≠
        periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 0 := by
    intro h
    have hij :=
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge_injective H h
    omega
  have h20 :
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 2 ≠
        periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 0 := by
    intro h
    have hij :=
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge_injective H h
    omega
  have h30 :
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 3 ≠
        periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 0 := by
    intro h
    have hij :=
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge_injective H h
    omega
  rw [
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge]
  unfold orientedFourEdgePlaquetteWord
  simp [periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomySection,
    h10, h20, h30]

/-- Hence the intrinsic primary-spatial plaquette holonomy is surjective onto
SU(2). -/
theorem periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_surjective_two
    (H : ℕ) :
    Surjective
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) := by
  intro U
  exact ⟨
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomySection H U,
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_section H U⟩

/-- Wilson energy of the primary plaquette as a continuous function on one
spatial slice. -/
noncomputable def periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyTwoContinuous
    (H : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) :=
  ⟨fun A =>
      specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)),
    by
      apply (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      fun_prop⟩

/-- The primary-spatial Wilson energy has infinite range already on one
spatial slice. -/
theorem periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyTwoContinuous_infiniteRange
    (H : ℕ) :
    (Set.range fun A =>
      periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyTwoContinuous H A).Infinite := by
  apply specialUnitaryWilsonPlaquetteEnergy_two_infiniteRange.mono
  rintro y ⟨U, rfl⟩
  rcases
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_surjective_two H U with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  change
    specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergy 2 U
  rw [hA]

/-- Normalized real trace of the primary spatial plaquette, represented as
`1 - E_W`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous
    (H : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) :=
  1 - periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyTwoContinuous H

/-- The one-slice continuous representative is exactly the normalized real
trace of the primary plaquette holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous_apply
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A =
      normalizedSpecialUnitaryRealTrace 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) := by
  change
    1 - specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) = _
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  ring

/-- The primary-spatial normalized trace has infinite range. -/
theorem periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous_infiniteRange
    (H : ℕ) :
    (Set.range fun A =>
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A).Infinite := by
  intro hTraceFinite
  have hEnergyInfinite :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyTwoContinuous_infiniteRange H
  apply hEnergyInfinite
  apply (hTraceFinite.image fun x : ℝ => 1 - x).subset
  rintro y ⟨A, rfl⟩
  refine ⟨
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A,
    ⟨A, rfl⟩, ?_⟩
  dsimp [periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous]
  ring

/-- Every finite initial normalized-trace power family has nonzero Gram
determinant after an arbitrary finite positive density change of one-slice Haar. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwo_withDensity_fin_gram_det_ne_zero
    (H : ℕ)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    (hw :
      AEMeasurable w
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
    (hw_ne_zero :
      ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2),
        w A ≠ 0)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)]
    (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^
            (j : ℕ)))).det ≠ 0 := by
  exact
    continuousMap_infiniteRange_powerFamily_toLp_withDensity_fin_gram_det_ne_zero
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      w hw hw_ne_zero
      (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H)
      (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous_infiniteRange H)
      k

end

end MathlibAnalytic
end MGAP4D
