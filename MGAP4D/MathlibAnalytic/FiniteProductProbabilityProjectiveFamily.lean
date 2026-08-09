import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Tactic

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

This is the pure Mathlib measure-theoretic core needed for the boundary-Haar
common carrier: no Wilson action, coupling, mass, or spectral input appears. -/
theorem finiteProductProbabilityMarginal_projective
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsProjectiveMeasureFamily (finiteProductProbabilityMarginal μ) := by
  classical
  intro I J hJI
  let r : (∀ i : I, α i) → (∀ j : J, α j) :=
    Finset.restrict₂ hJI
  have hr : Measurable r :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  refine Measure.pi_eq (μ := fun j : J => μ j) ?_
  intro s hs
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  let t : ∀ i : I, Set (α i) := fun i =>
    if hi : (i : ι) ∈ J then s ⟨i, hi⟩ else Set.univ
  have hpre :
      r ⁻¹' (Set.univ.pi s) = Set.univ.pi t := by
    ext x
    simp [r, t, Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  simp [t, measure_univ]

end

end MathlibAnalytic
end MGAP4D
