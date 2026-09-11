import MGAP4D.MathlibAnalytic.LinearMarkovInfinitePathMeasure
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFinitePathPrefixConsistency
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Finset MeasureTheory Preorder

noncomputable section

/-- A finite Wilson configuration space carries its canonical discrete
measurable structure: finiteness and measurable singletons make every subset
measurable. -/
local instance finiteLatticeWilsonConfigurationDiscreteMeasurableSpace
    (L : FiniteLatticeWilsonSystem) :
    DiscreteMeasurableSpace L.Configuration where
  forall_measurableSet s := Set.toFinite s |>.measurableSet

/-- The finite-prefix probability measure of the actual Gibbs-started Wilson
random-scan chain, indexed by natural times at most `n`. -/
def FiniteLatticeWilsonSystem.randomScanFiniteIicPathMeasure
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) : Measure (Finset.Iic n → L.Configuration) :=
  linearMarkovFiniteIicPathMeasure
    L.gibbsPMF L.randomScanTransitionPMF n

/-- The actual stationary infinite path probability measure of the finite
Wilson random-scan single-link heat-bath chain. -/
def FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    Measure (ℕ → L.Configuration) :=
  linearMarkovInfinitePathMeasure
    L.gibbsPMF L.randomScanTransitionPMF

instance finite_lattice_randomScanInfinitePathMeasure_isProbabilityMeasure
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    IsProbabilityMeasure L.randomScanInfinitePathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
  infer_instance

/-- Every natural prefix of the infinite Wilson random-scan path measure is the
corresponding finite-prefix measure. -/
theorem finite_lattice_randomScanInfinitePathMeasure_map_frestrictLe
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanInfinitePathMeasure.map (frestrictLe n) =
      L.randomScanFiniteIicPathMeasure n := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
    FiniteLatticeWilsonSystem.randomScanFiniteIicPathMeasure
  exact linearMarkovInfinitePathMeasure_map_frestrictLe
    L.gibbsPMF L.randomScanTransitionPMF n

/-- In the original `Fin` tuple representation, every honest finite Wilson
random-scan path PMF is exactly recovered from the infinite path measure. -/
theorem finite_lattice_randomScanInfinitePathMeasure_map_finPrefix
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanInfinitePathMeasure.map
        (linearMarkovInfinitePathFinPrefix n) =
      (L.randomScanFinitePathPMF n).toMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
    FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact linearMarkovInfinitePathMeasure_map_finPrefix
    L.gibbsPMF L.randomScanTransitionPMF n

/-- Every time coordinate of the actual infinite Wilson random-scan path has
exactly the finite Wilson Gibbs probability measure as its marginal. -/
theorem finite_lattice_randomScanInfinitePathMeasure_map_eval
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (i : ℕ) :
    L.randomScanInfinitePathMeasure.map (fun path => path i) =
      L.gibbsPMF.toMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
  exact
    linearMarkovInfinitePathMeasure_map_eval_of_expectation_stationary
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)
      i

end

end MathlibAnalytic
end MGAP4D
