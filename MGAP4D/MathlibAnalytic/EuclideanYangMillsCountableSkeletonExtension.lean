import MGAP4D.MathlibAnalytic.KolmogorovStandardBorelExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- Canonical probability measure on a countable standard-Borel skeleton. -/
noncomputable def countableSkeletonKolmogorovMeasure
    (Q : ∀ J : Finset κ, Measure (∀ k : J, β k))
    (hQprob : ∀ J, IsProbabilityMeasure (Q J))
    (hQproj : IsProjectiveMeasureFamily Q) :
    Measure (∀ k, β k) := by
  letI : ∀ J, IsProbabilityMeasure (Q J) := hQprob
  exact standardBorelKolmogorovProjectiveLimit Q hQproj

/-- The countable skeleton measure realizes its finite-dimensional laws. -/
theorem countableSkeletonKolmogorovMeasure_isProjectiveLimit
    (Q : ∀ J : Finset κ, Measure (∀ k : J, β k))
    (hQprob : ∀ J, IsProbabilityMeasure (Q J))
    (hQproj : IsProjectiveMeasureFamily Q) :
    IsProjectiveLimit
      (countableSkeletonKolmogorovMeasure Q hQprob hQproj) Q := by
  letI : ∀ J, IsProbabilityMeasure (Q J) := hQprob
  exact isProjectiveLimit_standardBorelKolmogorovProjectiveLimit hQproj

/-- The countable skeleton law is a probability measure. -/
theorem countableSkeletonKolmogorovMeasure_probability
    (Q : ∀ J : Finset κ, Measure (∀ k : J, β k))
    (hQprob : ∀ J, IsProbabilityMeasure (Q J))
    (hQproj : IsProjectiveMeasureFamily Q) :
    IsProbabilityMeasure
      (countableSkeletonKolmogorovMeasure Q hQprob hQproj) := by
  letI : ∀ J, IsProbabilityMeasure (Q J) := hQprob
  exact standardBorelKolmogorovProjectiveLimit_probability hQproj

/-- A countable standard-Borel skeleton together with a measurable
reconstruction of the full Euclidean field.  `finiteLawRecovery` is the exact
condition replacing the impossible demand for a countable cofinal family of
finite subsets of the uncountable spacetime index. -/
structure EuclideanYangMillsCountableSkeletonData
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (κ : Type*) [Countable κ] [Nonempty κ]
    (β : κ → Type*) [∀ k, MeasurableSpace (β k)]
    [∀ k, StandardBorelSpace (β k)] where
  skeletonMarginal :
    ∀ J : Finset κ, Measure (∀ k : J, β k)
  skeletonMarginalProbability :
    ∀ J, IsProbabilityMeasure (skeletonMarginal J)
  skeletonProjective :
    IsProjectiveMeasureFamily skeletonMarginal
  reconstruct : (∀ k, β k) → F.Configuration
  reconstructMeasurable : Measurable reconstruct
  finiteLawRecovery :
    ∀ J : Finset EuclideanFourSpace,
      (countableSkeletonKolmogorovMeasure
        skeletonMarginal skeletonMarginalProbability skeletonProjective).map
          (J.restrict ∘ reconstruct) =
        F.finiteMarginal J

/-- The countable skeleton product itself is standard Borel. -/
theorem countableSkeletonConfiguration_standardBorel
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (D : EuclideanYangMillsCountableSkeletonData F κ β) :
    StandardBorelSpace (∀ k, β k) := by
  infer_instance

/-- Push the countable skeleton law through the measurable reconstruction map. -/
noncomputable def EuclideanYangMillsCountableSkeletonData.continuumMeasure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (D : EuclideanYangMillsCountableSkeletonData F κ β) :
    Measure F.Configuration :=
  (countableSkeletonKolmogorovMeasure
    D.skeletonMarginal D.skeletonMarginalProbability D.skeletonProjective).map
      D.reconstruct

/-- The reconstructed measure realizes every finite Euclidean Yang--Mills law. -/
theorem EuclideanYangMillsCountableSkeletonData.isProjectiveLimit
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (D : EuclideanYangMillsCountableSkeletonData F κ β) :
    IsProjectiveLimit D.continuumMeasure F.finiteMarginal := by
  intro J
  calc
    D.continuumMeasure.map J.restrict =
        (countableSkeletonKolmogorovMeasure
          D.skeletonMarginal D.skeletonMarginalProbability
            D.skeletonProjective).map
          (J.restrict ∘ D.reconstruct) :=
      Measure.map_map J.measurable_restrict D.reconstructMeasurable
    _ = F.finiteMarginal J := D.finiteLawRecovery J

/-- Structure-level projective-limit measure reconstructed from the countable
skeleton. -/
noncomputable def EuclideanYangMillsCountableSkeletonData.projectiveLimitMeasure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (D : EuclideanYangMillsCountableSkeletonData F κ β) :
    EuclideanYangMillsProjectiveLimitMeasure F :=
  { continuumMeasure := D.continuumMeasure
    projectiveLimit := D.isProjectiveLimit }

/-- The reconstructed continuum law is a probability measure. -/
theorem EuclideanYangMillsCountableSkeletonData.continuumProbability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (D : EuclideanYangMillsCountableSkeletonData F κ β) :
    IsProbabilityMeasure D.continuumMeasure := by
  letI : IsProbabilityMeasure
      (countableSkeletonKolmogorovMeasure
        D.skeletonMarginal D.skeletonMarginalProbability
          D.skeletonProjective) :=
    countableSkeletonKolmogorovMeasure_probability
      D.skeletonMarginal D.skeletonMarginalProbability D.skeletonProjective
  exact Measure.isProbabilityMeasure_map D.reconstructMeasurable.aemeasurable

/-- Existence form of the countable-skeleton reconstruction route. -/
theorem EuclideanYangMillsCountableSkeletonData.projectiveLimitExists
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (D : EuclideanYangMillsCountableSkeletonData F κ β) :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  ⟨D.continuumMeasure, D.isProjectiveLimit⟩

end

end MathlibAnalytic
end MGAP4D
