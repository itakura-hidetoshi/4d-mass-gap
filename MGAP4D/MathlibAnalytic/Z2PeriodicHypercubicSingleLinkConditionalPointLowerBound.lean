import MGAP4D.MathlibAnalytic.FiniteNormalizedExponentialPointLowerBound
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalNormalizedExp
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Every plaquette energy in the periodic oriented `Z₂` Wilson system is at
most one. -/
theorem z2PeriodicHypercubicOrientedWilsonSystem_plaquetteEnergy_le_one
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (g : Z2Gauge) :
    FiniteOrientedLatticeWilsonSystem.plaquetteEnergy
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) g ≤ 1 := by
  change (if g = 1 then 0 else 1) ≤ 1
  split_ifs <;> norm_num

/-- The target-local periodic `Z₂` action is nonnegative. -/
theorem z2PeriodicHypercubic_targetLocalPlaquetteAction_nonneg
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration)
    (target : PeriodicHypercubicEdge n) :
    0 ≤ FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) A target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
  apply Finset.sum_nonneg
  intro p _hp
  by_cases hTouch :
      FiniteOrientedLatticeWilsonSystem.PlaquetteTouchesEdge
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p target
  · simp only [if_pos hTouch]
    exact FiniteOrientedLatticeWilsonSystem.plaquetteEnergy_nonneg
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) _
  · simp [hTouch]

/-- At most six unit-energy plaquettes contribute to the target-local action. -/
theorem z2PeriodicHypercubic_targetLocalPlaquetteAction_le_six
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration)
    (target : PeriodicHypercubicEdge n) :
    FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) A target ≤ 6 := by
  classical
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let targetL : L.Edge := target
  have hTouchingFinset :
      (Finset.univ.filter fun p : L.Plaquette =>
          L.PlaquetteTouchesEdge p targetL) =
        periodicHypercubicTouchingPlaquettes n target := by
    apply Finset.ext
    intro p
    rw [Finset.mem_filter, periodicHypercubic_mem_touchingPlaquettes_iff]
    simp only [Finset.mem_univ, true_and]
    change periodicHypercubicPlaquetteTouchesEdge n p target ↔
      periodicHypercubicPlaquetteTouchesEdge n p target
    rfl
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
  change (∑ p : L.Plaquette,
      if L.PlaquetteTouchesEdge p targetL then
        L.plaquetteEnergy (L.plaquetteHolonomy A p)
      else 0) ≤ 6
  calc
    (∑ p : L.Plaquette,
        if L.PlaquetteTouchesEdge p targetL then
          L.plaquetteEnergy (L.plaquetteHolonomy A p)
        else 0) ≤
      ∑ p : L.Plaquette,
        if L.PlaquetteTouchesEdge p targetL then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p _hp
      by_cases hTouch : L.PlaquetteTouchesEdge p targetL
      · simp only [if_pos hTouch]
        exact z2PeriodicHypercubicOrientedWilsonSystem_plaquetteEnergy_le_one
          n beta hBeta _
      · simp [hTouch]
    _ = ((Finset.univ.filter fun p : L.Plaquette =>
          L.PlaquetteTouchesEdge p targetL).card : ℝ) := by
      simp
    _ = ((periodicHypercubicTouchingPlaquettes n target).card : ℝ) := by
      simpa using congrArg
        (fun s : Finset L.Plaquette => (s.card : ℝ)) hTouchingFinset
    _ ≤ 6 := by
      exact_mod_cast periodicHypercubicTouchingPlaquettes_card_le_six n target

/-- The target-local log-weight oscillation is at most `6 * beta`, uniformly in
the periodic volume and exterior configuration. -/
theorem z2PeriodicHypercubic_targetLocalSingleLinkLogWeight_oscillation
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration)
    (target : PeriodicHypercubicEdge n)
    (g h : Z2Gauge) :
    FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) A target g -
        FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) A target h ≤
      6 * beta := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let actionG := L.targetLocalPlaquetteAction (L.replaceLink A target g) target
  let actionH := L.targetLocalPlaquetteAction (L.replaceLink A target h) target
  have hActionGNonneg : 0 ≤ actionG :=
    z2PeriodicHypercubic_targetLocalPlaquetteAction_nonneg
      n beta hBeta (L.replaceLink A target g) target
  have hActionHLe : actionH ≤ 6 :=
    z2PeriodicHypercubic_targetLocalPlaquetteAction_le_six
      n beta hBeta (L.replaceLink A target h) target
  have hDifference : actionH - actionG ≤ 6 := by
    linarith
  change -beta * actionG - (-beta * actionH) ≤ 6 * beta
  calc
    -beta * actionG - (-beta * actionH) = beta * (actionH - actionG) := by
      ring
    _ ≤ beta * 6 := mul_le_mul_of_nonneg_left hDifference hBeta
    _ = 6 * beta := by ring

/-- Every exact periodic `Z₂` one-link conditional atom has the volume-independent
lower bound `exp(-6 * beta) / 2`. -/
theorem z2PeriodicHypercubic_singleLinkConditionalPMF_toReal_lower
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration)
    (target : PeriodicHypercubicEdge n)
    (g : Z2Gauge) :
    Real.exp (-(6 * beta)) / 2 ≤
      (FiniteOrientedLatticeWilsonSystem.singleLinkConditionalPMF
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        A target g).toReal := by
  rw [finite_oriented_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp]
  apply z2Gauge_finiteNormalizedExp_lower_of_oscillation
  intro x y
  exact z2PeriodicHypercubic_targetLocalSingleLinkLogWeight_oscillation
    n beta hBeta A target x y

end

end MathlibAnalytic
end MGAP4D
