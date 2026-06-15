import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishKolmogorovExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishKolmogorovCondition
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsPolishKolmogorovExtension

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}
  [∀ J, IsFiniteMeasure (P J)]

/-- Compile gate: Polish finite-dimensional projective laws have a projective
limit. -/
theorem kolmogorov_polish_exists_compile_smoke
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ P :=
  kolmogorov_projective_limit_exists hP

/-- Compile gate: the explicit Carathéodory extension recovers all finite laws. -/
theorem kolmogorov_polish_isProjectiveLimit_compile_smoke
    (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (kolmogorovProjectiveLimit P hP) P :=
  isProjectiveLimit_kolmogorovProjectiveLimit hP

/-- Compile gate: projective probability laws yield a probability measure. -/
theorem kolmogorov_polish_probability_compile_smoke
    [Nonempty ι] [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    IsProbabilityMeasure (kolmogorovProjectiveLimit P hP) := by
  infer_instance

/-- Compile gate: the Euclidean Yang--Mills specialization exists. -/
theorem euclidean_yang_mills_polish_exists_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  euclidean_yang_mills_polish_projective_limit_exists

/-- Compile gate: Polish tightness supplies the abstract cylinder-continuity
condition used by the Carathéodory extension theorem. -/
theorem euclidean_yang_mills_polish_condition_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] :
    EuclideanYangMillsKolmogorovExtensionCondition F :=
  euclideanYangMillsPolishKolmogorovExtensionCondition F

/-- Compile gate: the abstract continuity construction and the direct Polish
construction define the same measure. -/
theorem euclidean_yang_mills_polish_constructions_agree_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] :
    euclideanYangMillsKolmogorovMeasure
        (euclideanYangMillsPolishKolmogorovExtensionCondition F) =
      euclideanYangMillsPolishKolmogorovMeasure F :=
  euclidean_yang_mills_condition_measure_eq_polish_measure

/-- Compile gate: direct coarse-graining Wilson marginals admit a Polish
Kolmogorov extension. -/
theorem finite_wilson_coherent_polish_exists_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  finite_wilson_gibbs_coherent_polish_projective_limit_exists R

/-- Compile gate: common-refinement Wilson marginals admit a Polish
Kolmogorov extension. -/
theorem finite_wilson_common_refinement_polish_exists_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  finite_wilson_gibbs_common_refinement_polish_projective_limit_exists R

/-- Compile gate: the direct single-source and Polish extensions coincide. -/
theorem finite_wilson_single_source_direct_eq_polish_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    R.continuumMeasure =
      euclideanYangMillsPolishKolmogorovMeasure
        R.toProjectiveRealization.toProjectiveCylinderFamily :=
  finite_wilson_gibbs_single_source_direct_eq_polish R

end

end MathlibAnalytic
end MGAP4D
