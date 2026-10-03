import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityFourEdgeMoment
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightTraceGram
import Mathlib.Tactic

/-!
# H1-D5 half-weight endpoint measure inherits genuine four-edge Gram strictness

The preceding one-slice theorem works for every finite density which is
nonzero almost everywhere.  This file specializes it to the literal spatial
half-Boltzmann density already used by the H1-D5 positive-density crossing
formulation.

Thus every nonzero finite primary normalized-trace polynomial is detected, in
the exact H1-D5 endpoint measure, by a strictly positive genuine four-edge
degree Gram contribution.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

local instance h1d5HalfWeightFourEdgeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance h1d5HalfWeightFourEdgeCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance h1d5HalfWeightFourEdgeSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance h1d5HalfWeightFourEdgeMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance h1d5HalfWeightFourEdgeBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance h1d5HalfWeightFourEdgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact H1-D5 half-weight endpoint measure preserves the positive-degree
four-edge Gram witness for every nonzero finite primary trace polynomial. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_halfWeightMeasure_exists_positiveDegree_fourEdgeGram_pos
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0) :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      0 <
        ∫ A₁, ∫ A₂,
          inner ℝ
            (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₁ •
              (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature
                H ((i : ℕ) + 1)).feature A₁)
            (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₂ •
              (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature
                H ((i : ℕ) + 1)).feature A₂)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) := by
  let w :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H 2 beta
  letI hfin : IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
    simpa [w, periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_isFiniteMeasure
        H 2 (by norm_num : 0 < (2 : ℕ)) beta hbeta
  have hStrict :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_withDensity_exists_positiveDegree_fourEdgeGram_pos
      H k c hc w
      (by
        simpa [w] using
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
            H 2 beta).aemeasurable)
      (Filter.Eventually.of_forall
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_ne_zero
          H 2 beta))
  simpa [w,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure] using hStrict

end

end MathlibAnalytic
end MGAP4D
