import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathMeasure
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanIntegerCenteredPathProjectiveFamily

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The actual finite-dimensional Gibbs-stationary random-scan law on an arbitrary
finite set of integer times. -/
abbrev FiniteLatticeWilsonSystem.randomScanIntegerFiniteMarginalPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (J : Finset ℤ) : PMF (∀ _t : J, L.Configuration) :=
  linearMarkovIntegerFiniteMarginalPMF
    L.gibbsPMF L.randomScanTransitionPMF J

/-- The actual finite-dimensional random-scan marginal as a probability measure. -/
noncomputable abbrev
    FiniteLatticeWilsonSystem.randomScanIntegerFiniteMarginalMeasure
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (J : Finset ℤ) : Measure (∀ _t : J, L.Configuration) :=
  linearMarkovIntegerFiniteMarginalMeasure
    L.gibbsPMF L.randomScanTransitionPMF J

/-- The actual finite Wilson integer-time marginals form a projective family. -/
theorem finite_lattice_randomScanIntegerFiniteMarginalMeasure_projective
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    IsProjectiveMeasureFamily (α := fun _ : ℤ => L.Configuration)
      L.randomScanIntegerFiniteMarginalMeasure := by
  exact linearMarkovIntegerFiniteMarginalMeasure_projective
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L)

/-- The countably additive two-sided integer-time path measure of the actual
Gibbs-stationary finite Wilson random-scan chain. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathMeasure
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] : Measure (ℤ → L.Configuration) :=
  linearMarkovTwoSidedIntegerPathMeasure
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L)

/-- Every prescribed actual finite Wilson integer-time marginal is recovered
exactly from the two-sided path measure. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathMeasure_isProjectiveLimit
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    IsProjectiveLimit (α := fun _ : ℤ => L.Configuration)
      L.randomScanTwoSidedIntegerPathMeasure
      L.randomScanIntegerFiniteMarginalMeasure := by
  exact linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L)

/-- The actual two-sided finite Wilson random-scan path law is a probability
measure. -/
instance finiteLatticeWilsonSystem_randomScanTwoSidedIntegerPathMeasure_isProbability
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    IsProbabilityMeasure L.randomScanTwoSidedIntegerPathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathMeasure
  infer_instance

end

end MathlibAnalytic
end MGAP4D
