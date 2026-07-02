import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteExpectationFiniteGibbs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PeriodicHypercubicPlaquetteTrajectory

/-- A canonical representative of the fixed finite lattice at zero coupling.
Only the coupling field changes in `systemAtBeta`; its configuration carrier,
plaquette energy, and Wilson action are fixed. -/
noncomputable def fixedSystem
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    FiniteOrientedLatticeWilsonSystem :=
  T.systemAtBeta k 0 (by positivity)

noncomputable local instance fixedSystemConfigurationFintype
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    Fintype (T.fixedSystem k).Configuration :=
  Fintype.ofFinite (T.fixedSystem k).Configuration

/-- The selected plaquette observable on the canonical fixed system. -/
noncomputable def fixedPlaquetteObservable
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    (T.fixedSystem k).Configuration -> Real :=
  T.plaquetteObservableAtBeta k 0 (by positivity)

/-- The Wilson action on the canonical fixed system. -/
noncomputable def fixedWilsonAction
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    (T.fixedSystem k).Configuration -> Real :=
  (T.fixedSystem k).wilsonAction

/-- The fixed-lattice plaquette expectation as a real function of an arbitrary
coupling. -/
noncomputable def fixedPlaquetteGibbsExpectation
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) : Real :=
  FiniteGibbsExpectationBetaDerivative.expectation
    (T.fixedPlaquetteObservable k) (T.fixedWilsonAction k) beta

/-- At every nonnegative coupling, the trajectory expectation is represented by
the canonical fixed-lattice Gibbs expectation. -/
theorem plaquetteExpectationAtBeta_eq_fixedPlaquetteGibbsExpectation
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) (hBeta : 0 <= beta) :
    T.plaquetteExpectationAtBeta k beta hBeta =
      T.fixedPlaquetteGibbsExpectation k beta := by
  rw [T.plaquetteExpectationAtBeta_eq_finiteGibbsExpectation]
  rfl

end Z2PeriodicHypercubicPlaquetteTrajectory

end

end MathlibAnalytic
end MGAP4D
