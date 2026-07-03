import MGAP4D.MathlibAnalytic.PeriodicHypercubicAutomaticL1SpatialCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The periodic four-dimensional hypercubic lattice has a physical positive
link for every nonzero side length. -/
theorem periodicHypercubicEdge_card_pos
    (n : ℕ) [NeZero n] :
    0 < Fintype.card (PeriodicHypercubicEdge n) := by
  exact Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩

/-- The canonical Dobrushin coefficient for the periodic `Z₂` Wilson system,
with the edge nonemptiness proof supplied internally from `[NeZero n]`. -/
noncomputable def
    z2PeriodicHypercubicCanonicalDobrushinCoefficient
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta) : ℝ :=
  FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
    (periodicHypercubicEdge_card_pos n)

/-- The internally supplied canonical coefficient is definitionally the
coefficient used by the preceding automatic spatial covariance theorem. -/
@[simp] theorem
    z2PeriodicHypercubicCanonicalDobrushinCoefficient_eq
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta =
      FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (periodicHypercubicEdge_card_pos n) :=
  rfl

/-- Canonical finite-volume periodic `Z₂` plaquette covariance decay with both
the geometric exponent and the edge nonemptiness certificate chosen
internally.  The remaining substantive hypothesis is strictness of the exact
canonical Dobrushin coefficient. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1_of_canonicalStrict
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hStrict :
      z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta < 1) :
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      16 *
        (z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicCanonicalDobrushinCoefficient
              n beta hBeta)) := by
  exact
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1
      n beta hBeta sourcePlaquette targetPlaquette
      (periodicHypercubicEdge_card_pos n) hStrict

end

end MathlibAnalytic
end MGAP4D
