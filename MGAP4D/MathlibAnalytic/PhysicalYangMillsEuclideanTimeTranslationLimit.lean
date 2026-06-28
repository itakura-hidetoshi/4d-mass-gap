import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

structure PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) where
  translate : ℝ → Homeomorph S.Configuration S.Configuration
  translate_zero_apply : ∀ A, translate 0 A = A
  translate_add_apply : ∀ s t A,
    translate (s + t) A = translate s (translate t A)
  gauge_commute : ∀ t g A,
    translate t (S.action g A) = S.action g (translate t A)
  approximatingInvariant : ∀ n t,
    (S.approximatingMeasure n).map
        (translate t).continuous.measurable.aemeasurable =
      S.approximatingMeasure n

namespace PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}

theorem translate_symm_apply_eq_neg
    (E : PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit S)
    (t : ℝ) (A : S.Configuration) :
    (E.translate t).symm A = E.translate (-t) A := by
  apply (E.translate t).injective
  rw [Homeomorph.apply_symm_apply]
  rw [← E.translate_add_apply]
  simpa using (E.translate_zero_apply A).symm

theorem continuumProbabilityMeasure_map_eq_self
    (E : PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit S)
    (t : ℝ) :
    S.continuumMeasure.map
        (E.translate t).continuous.measurable.aemeasurable =
      S.continuumMeasure := by
  have hMapped :
      Tendsto
        (fun n : ℕ =>
          (S.approximatingMeasure n).map
            (E.translate t).continuous.measurable.aemeasurable)
        atTop
        (nhds
          (S.continuumMeasure.map
            (E.translate t).continuous.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      S.approximatingMeasure S.continuumMeasure
      S.weakConvergence (E.translate t).continuous
  have hOriginal :
      Tendsto
        (fun n : ℕ =>
          (S.approximatingMeasure n).map
            (E.translate t).continuous.measurable.aemeasurable)
        atTop
        (nhds S.continuumMeasure) := by
    simpa only [E.approximatingInvariant] using S.weakConvergence
  exact tendsto_nhds_unique hMapped hOriginal

theorem continuumMeasure_map_eq_self
    (E : PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit S)
    (t : ℝ) :
    Measure.map (E.translate t)
        (S.continuumMeasure : Measure S.Configuration) =
      (S.continuumMeasure : Measure S.Configuration) := by
  have h := congrArg ProbabilityMeasure.toMeasure
    (E.continuumProbabilityMeasure_map_eq_self t)
  simpa only [ProbabilityMeasure.toMeasure_map] using h

end PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit

end

end MathlibAnalytic
end MGAP4D
