import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathGibbsPairing
import Mathlib.Tactic

/-!
# Gibbs covariance invariance for finite current heat-bath schedules

The finite compact Wilson carrier already has the two exact identities needed
for covariance preservation under a finite ordered heat-bath schedule:

* the canonical Gibbs mean is stationary under the actual finite heat-bath
  kernel;
* if the left observable is constant on every updated link fiber, inserting the
  same finite heat-bath action in the right slot leaves the Gibbs pairing
  unchanged.

This file packages those two identities in a named finite-volume real Gibbs
mean and covariance API and proves the corresponding covariance invariance.
The proof is purely algebraic once the two current heat-bath theorems are in
place.

No covariance decay estimate is asserted here.  In particular, update count is
not identified with Euclidean time, and no continuum clustering, positive
physical mass, OS Hamiltonian gap, or uniform factorial-continuum Dobrushin
threshold is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Canonical finite-volume Wilson Gibbs mean of a real observable. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ) : ℝ :=
  ∫ A, f A ∂C.gibbsMeasure

/-- Canonical finite-volume real Gibbs covariance, expressed through the
existing Gibbs pairing and the Gibbs means. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.base.Configuration → ℝ) : ℝ :=
  C.gibbsPairingReal f g - C.gibbsMeanReal f * C.gibbsMeanReal g

/-- The actual finite ordered current heat-bath action preserves the canonical
finite-volume Wilson Gibbs mean of every bounded continuous observable. -/
theorem continuous_compact_oriented_gibbsMeanReal_finiteSingleLinkHeatBathExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsMeanReal
        (fun A => C.finiteSingleLinkHeatBathExpectationBCF targets O A) =
      C.gibbsMeanReal (fun A => O A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
  exact
    continuous_compact_oriented_gibbs_integral_finiteSingleLinkHeatBathExpectationBCF
      C targets O

/-- If the left bounded-continuous observable is constant on every physical
link fiber updated by a finite ordered heat-bath schedule, then the actual
finite heat-bath action on the right leaves the finite-volume Gibbs covariance
unchanged. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_finiteSingleLinkHeatBathExpectationBCF_eq_of_left_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hFiber : ∀ target ∈ targets,
      C.base.OffLinkFiberConstant target (fun A => F A)) :
    C.gibbsCovarianceReal (fun A => F A)
        (fun A => C.finiteSingleLinkHeatBathExpectationBCF targets O A) =
      C.gibbsCovarianceReal (fun A => F A) (fun A => O A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [
    continuous_compact_oriented_gibbsPairing_finiteSingleLinkHeatBathExpectationBCF_eq_of_left_offLinkFiberConstant
      C targets F O hFiber,
    continuous_compact_oriented_gibbsMeanReal_finiteSingleLinkHeatBathExpectationBCF
      C targets O]

end

end MathlibAnalytic
end MGAP4D
