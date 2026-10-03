import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityGram
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModePositiveDensityCrossingGram
import Mathlib.Tactic

/-!
# H1-D5 endpoint measure has nondegenerate primary trace-power Gram families

The positive-density crossing formulation from #5048 uses the one-slice Haar
measure tilted by the literal positive spatial half-Boltzmann weight.

The one-slice positive-density theorem applies to that exact density.  Hence
every finite initial family of powers of the primary plaquette normalized trace
has nonzero Gram determinant in precisely the endpoint measure occurring in the
remaining H1-D5 crossing integral.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

local instance h1d5HalfWeightTraceGramTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance h1d5HalfWeightTraceGramCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance h1d5HalfWeightTraceGramSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance h1d5HalfWeightTraceGramMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance h1d5HalfWeightTraceGramBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance h1d5HalfWeightTraceGramSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical continuous-to-L2 map for the exact half-weight endpoint measure.
The finite-measure certificate is carried explicitly by `hbeta`, so later theorem
statements do not rely on typeclass synthesis unfolding the half-weight measure alias. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightContinuousToLp
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) →L[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) := by
  letI : IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_isFiniteMeasure
      H 2 (by norm_num : 0 < (2 : ℕ)) beta hbeta
  exact ContinuousMap.toLp
    (E := ℝ) 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) ℝ

/-- Every finite initial primary normalized-trace power family is Gram
nondegenerate in the exact half-weight endpoint measure used by #5048. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwo_halfWeightMeasure_fin_gram_det_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightContinuousToLp
          H beta hbeta
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^
            (j : ℕ)))).det ≠ 0 := by
  let w :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H 2 beta
  letI hfinHalf : IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_isFiniteMeasure
      H 2 (by norm_num : 0 < (2 : ℕ)) beta hbeta
  letI hfinDensity : IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
    simpa [w, periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure] using hfinHalf
  have hdet :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwo_withDensity_fin_gram_det_ne_zero
      H w
      (by
        simpa [w] using
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
            H 2 beta).aemeasurable)
      (Filter.Eventually.of_forall
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_ne_zero
          H 2 beta))
      k
  change
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^
            (j : ℕ)))).det ≠ 0
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure
  simpa [w] using hdet

end

end MathlibAnalytic
end MGAP4D
