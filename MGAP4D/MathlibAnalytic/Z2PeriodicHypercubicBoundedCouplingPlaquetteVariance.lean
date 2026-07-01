import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteEnergyVarianceLowerBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A uniform upper bound on the coupling converts the explicit fixed-coupling
plaquette variance estimate into a common lower bound. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_lower_of_beta_le
    (n : ℕ) [NeZero n]
    (hn : 2 ≤ n)
    (beta B : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLe : beta ≤ B)
    (p : PeriodicHypercubicPlaquette n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    Real.exp (-(6 * B)) / 8 ≤
      L.gibbsVarianceReal
        (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p) := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  change Real.exp (-(6 * B)) / 8 ≤
    L.gibbsVarianceReal
      (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p)
  have hExponent : -(6 * B) ≤ -(6 * beta) := by
    nlinarith
  have hExp : Real.exp (-(6 * B)) ≤ Real.exp (-(6 * beta)) :=
    Real.exp_le_exp.mpr hExponent
  have hScaled : Real.exp (-(6 * B)) / 8 ≤ Real.exp (-(6 * beta)) / 8 :=
    div_le_div_of_nonneg_right hExp (by norm_num)
  exact hScaled.trans
    (z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_lower
      n hn beta hBeta p)

/-- Along any periodic `Z₂` lattice sequence whose couplings are bounded above
by `B`, the selected gauge-invariant plaquette energies have the common
finite-volume variance lower bound `exp(-6B) / 8`. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_sequence_uniform_variance_lower
    (side : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (B : ℝ)
    (hSide : ∀ k, 2 ≤ side k)
    (hBeta : ∀ k, 0 ≤ beta k)
    (hBetaLe : ∀ k, beta k ≤ B)
    (p : ∀ k, PeriodicHypercubicPlaquette (side k)) :
    ∀ k,
      letI : NeZero (side k) := ⟨by
        exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two (hSide k))⟩
      let L := z2PeriodicHypercubicOrientedWilsonSystem
        (side k) (beta k) (hBeta k)
      Real.exp (-(6 * B)) / 8 ≤
        L.gibbsVarianceReal
          (z2PeriodicHypercubicPlaquetteEnergyObservable
            (side k) (beta k) (hBeta k) (p k)) := by
  intro k
  letI : NeZero (side k) := ⟨by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two (hSide k))⟩
  exact
    z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_lower_of_beta_le
      (side k) (hSide k) (beta k) B (hBeta k) (hBetaLe k) (p k)

/-- The common bounded-coupling lower bound is strictly positive. -/
theorem z2PeriodicHypercubic_boundedCouplingVarianceLowerBound_pos
    (B : ℝ) :
    0 < Real.exp (-(6 * B)) / 8 := by
  positivity

end

end MathlibAnalytic
end MGAP4D
