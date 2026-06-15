import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

/-- Kolmogorov extension for standard Borel coordinate spaces. Each coordinate
is equipped locally with the compatible Polish topology supplied by
`upgradeStandardBorel`; the resulting measure lives on the original measurable
product space. -/
noncomputable def standardBorelKolmogorovProjectiveLimit
    [∀ i, StandardBorelSpace (α i)]
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    Measure (∀ i, α i) := by
  letI := fun i => upgradeStandardBorel (α i)
  exact kolmogorovProjectiveLimit P hP

/-- The standard Borel extension realizes every prescribed finite-dimensional
law. -/
theorem isProjectiveLimit_standardBorelKolmogorovProjectiveLimit
    [∀ i, StandardBorelSpace (α i)]
    [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit
      (standardBorelKolmogorovProjectiveLimit P hP) P := by
  letI := fun i => upgradeStandardBorel (α i)
  exact isProjectiveLimit_kolmogorovProjectiveLimit hP

/-- Existence form of the standard Borel Kolmogorov theorem. -/
theorem standardBorel_kolmogorov_projective_limit_exists
    [∀ i, StandardBorelSpace (α i)]
    [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ P :=
  ⟨standardBorelKolmogorovProjectiveLimit P hP,
    isProjectiveLimit_standardBorelKolmogorovProjectiveLimit hP⟩

/-- Probability normalization passes to the standard Borel extension. -/
theorem standardBorelKolmogorovProjectiveLimit_probability
    [Nonempty ι]
    [∀ i, StandardBorelSpace (α i)]
    [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    IsProbabilityMeasure
      (standardBorelKolmogorovProjectiveLimit P hP) := by
  letI := fun i => upgradeStandardBorel (α i)
  exact MeasureTheory.IsProjectiveLimit.isProbabilityMeasure
    (isProjectiveLimit_kolmogorovProjectiveLimit hP)

end

end MathlibAnalytic
end MGAP4D
