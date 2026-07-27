import MGAP4D.MathlibAnalytic.LinearMarkovIntegerFiniteMarginalPMF
import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

local instance linearMarkovIntegerDiscreteTopology : TopologicalSpace Ω := ⊥

local instance linearMarkovIntegerDiscreteTopology_isDiscrete : DiscreteTopology Ω :=
  ⟨rfl⟩

local instance linearMarkovIntegerDiscreteBorelSpace : BorelSpace Ω := by
  infer_instance

local instance linearMarkovIntegerDiscretePolishSpace : PolishSpace Ω := by
  infer_instance

/-- The finite-dimensional integer-time marginal as a probability measure. -/
noncomputable def linearMarkovIntegerFiniteMarginalMeasure
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (J : Finset ℤ) : Measure (∀ _t : J, Ω) :=
  (linearMarkovIntegerFiniteMarginalPMF initial transition J).toMeasure

instance linearMarkovIntegerFiniteMarginalMeasure_isProbability
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (J : Finset ℤ) :
    IsProbabilityMeasure
      (linearMarkovIntegerFiniteMarginalMeasure initial transition J) := by
  unfold linearMarkovIntegerFiniteMarginalMeasure
  infer_instance

/-- Restriction between finite constant products is measurable. -/
theorem linearMarkovIntegerFiniteSetRestrict_measurable
    {I J : Finset ℤ} (hJI : J ⊆ I) :
    Measurable
      (linearMarkovIntegerFiniteSetRestrict hJI :
        (∀ _t : I, Ω) → (∀ _t : J, Ω)) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The PMF projectivity theorem induces a projective family of finite Borel
probability measures. -/
theorem linearMarkovIntegerFiniteMarginalMeasure_projective
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ => Ω)
      (linearMarkovIntegerFiniteMarginalMeasure initial transition) := by
  intro I J hJI
  have hpmf := linearMarkovIntegerFiniteMarginalPMF_projective_restrict
    initial transition hdb I J hJI
  change
    (linearMarkovIntegerFiniteMarginalPMF initial transition J).toMeasure =
      ((linearMarkovIntegerFiniteMarginalPMF initial transition I).toMeasure).map
        (linearMarkovIntegerFiniteSetRestrict hJI)
  rw [hpmf]
  simpa using
    (PMF.toMeasure_map
      (p := linearMarkovIntegerFiniteMarginalPMF initial transition I)
      (f := linearMarkovIntegerFiniteSetRestrict hJI)
      (linearMarkovIntegerFiniteSetRestrict_measurable hJI))

/-- The countably additive two-sided integer-time path law supplied by the Polish
Kolmogorov extension theorem. -/
noncomputable def linearMarkovTwoSidedIntegerPathMeasure
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    Measure (ℤ → Ω) :=
  kolmogorovProjectiveLimit (α := fun _ : ℤ => Ω)
    (linearMarkovIntegerFiniteMarginalMeasure initial transition)
    (linearMarkovIntegerFiniteMarginalMeasure_projective
      initial transition hdb)

/-- Every prescribed finite integer-time marginal is recovered exactly from the
two-sided path measure. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    IsProjectiveLimit (α := fun _ : ℤ => Ω)
      (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb)
      (linearMarkovIntegerFiniteMarginalMeasure initial transition) := by
  exact isProjectiveLimit_kolmogorovProjectiveLimit
    (α := fun _ : ℤ => Ω)
    (linearMarkovIntegerFiniteMarginalMeasure_projective
      initial transition hdb)

instance linearMarkovTwoSidedIntegerPathMeasure_isProbability
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    IsProbabilityMeasure
      (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb) := by
  unfold linearMarkovTwoSidedIntegerPathMeasure
  infer_instance

end

end MathlibAnalytic
end MGAP4D
