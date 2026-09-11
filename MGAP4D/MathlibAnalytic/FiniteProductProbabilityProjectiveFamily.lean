import Mathlib.Probability.ProductMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable
    {ι : Type*}
    {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]

/-- The finite marginal obtained by taking the dependent product of a family of
probability measures over one finite coordinate set. -/
noncomputable def finiteProductProbabilityMarginal
    (μ : ∀ i, Measure (α i))
    (J : Finset ι) :
    Measure (∀ j : J, α j) :=
  Measure.pi (fun j : J => μ j)

/-- Finite products of probability measures are again probability measures. -/
instance finiteProductProbabilityMarginal_isProbabilityMeasure
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (J : Finset ι) :
    IsProbabilityMeasure (finiteProductProbabilityMarginal μ J) := by
  unfold finiteProductProbabilityMarginal
  infer_instance

/-- Finite dependent products of one coordinatewise probability law form a
projective family under coordinate restriction.

This is exactly Mathlib's product-probability projectivity theorem.  Keeping the
repository wrapper gives the Wilson-facing layer a stable name while leaving
all measure-theoretic ownership in Mathlib. -/
theorem finiteProductProbabilityMarginal_projective
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsProjectiveMeasureFamily (finiteProductProbabilityMarginal μ) := by
  exact isProjectiveMeasureFamily_pi μ

/-- The arbitrary product probability measure is a genuine projective limit of
the finite product marginals. -/
theorem finiteProductProbabilityMarginal_infinitePi_projectiveLimit
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsProjectiveLimit (Measure.infinitePi μ)
      (finiteProductProbabilityMarginal μ) := by
  exact Measure.isProjectiveLimit_infinitePi μ

end

end MathlibAnalytic
end MGAP4D
