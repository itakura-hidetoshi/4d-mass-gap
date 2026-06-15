import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {F : EuclideanYangMillsProjectiveCylinderFamily}
  [∀ x, TopologicalSpace (F.fieldValue x)]
  [∀ x, BorelSpace (F.fieldValue x)]
  [∀ x, PolishSpace (F.fieldValue x)]

/-- The Kolmogorov extension measure associated with a Euclidean Yang--Mills
projective family whose coordinate spaces are Polish Borel spaces. -/
noncomputable def euclideanYangMillsPolishKolmogorovMeasure
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] :
    Measure F.Configuration := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact kolmogorovProjectiveLimit F.finiteMarginal F.projective

/-- The Polish Kolmogorov measure realizes every prescribed finite-dimensional
Euclidean Yang--Mills marginal. -/
theorem euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit :
    IsProjectiveLimit (euclideanYangMillsPolishKolmogorovMeasure F)
      F.finiteMarginal := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact isProjectiveLimit_kolmogorovProjectiveLimit F.projective

/-- General Kolmogorov existence theorem specialized to the typed Euclidean
Yang--Mills projective family. -/
theorem euclidean_yang_mills_polish_projective_limit_exists :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  ⟨euclideanYangMillsPolishKolmogorovMeasure F,
    euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit⟩

/-- Structure-level projective-limit existence. -/
theorem euclidean_yang_mills_polish_projective_limit_nonempty :
    Nonempty (EuclideanYangMillsProjectiveLimitMeasure F) :=
  ⟨{ continuumMeasure := euclideanYangMillsPolishKolmogorovMeasure F
     projectiveLimit :=
       euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit }⟩

/-- The Polish Kolmogorov extension is a probability measure. -/
theorem euclidean_yang_mills_polish_kolmogorov_probability :
    IsProbabilityMeasure (euclideanYangMillsPolishKolmogorovMeasure F) := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact MeasureTheory.IsProjectiveLimit.isProbabilityMeasure
    euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit

/-- Every measurable cylinder has exactly the prescribed finite-dimensional
probability. -/
theorem euclidean_yang_mills_polish_kolmogorov_cylinder
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, F.fieldValue x)}
    (hs : MeasurableSet s) :
    euclideanYangMillsPolishKolmogorovMeasure F (cylinder J s) =
      F.finiteMarginal J s :=
  euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit.measure_cylinder J hs

/-- The Polish Kolmogorov extension is the unique measure with the prescribed
finite-dimensional laws. -/
theorem euclidean_yang_mills_polish_kolmogorov_unique
    (ν : Measure F.Configuration)
    (hν : IsProjectiveLimit ν F.finiteMarginal) :
    ν = euclideanYangMillsPolishKolmogorovMeasure F := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact hν.unique euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit

/-- Audit-visible certificate for the Euclidean Yang--Mills Polish Kolmogorov
extension route. -/
structure EuclideanYangMillsPolishKolmogorovCertificate
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] where
  projectiveLimit :
    IsProjectiveLimit (euclideanYangMillsPolishKolmogorovMeasure F)
      F.finiteMarginal
  probability :
    IsProbabilityMeasure (euclideanYangMillsPolishKolmogorovMeasure F)
  finiteMarginalsRecovered :
    ∀ J : Finset EuclideanFourSpace,
      (euclideanYangMillsPolishKolmogorovMeasure F).map J.restrict =
        F.finiteMarginal J
  unique :
    ∀ ν : Measure F.Configuration,
      IsProjectiveLimit ν F.finiteMarginal →
        ν = euclideanYangMillsPolishKolmogorovMeasure F

/-- Construct the Euclidean Yang--Mills Polish Kolmogorov certificate. -/
def euclideanYangMillsPolishKolmogorovCertificate
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] :
    EuclideanYangMillsPolishKolmogorovCertificate F :=
  { projectiveLimit :=
      euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit
    probability := euclidean_yang_mills_polish_kolmogorov_probability
    finiteMarginalsRecovered :=
      euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit
    unique := fun ν hν =>
      euclidean_yang_mills_polish_kolmogorov_unique ν hν }

end

end MathlibAnalytic
end MGAP4D
