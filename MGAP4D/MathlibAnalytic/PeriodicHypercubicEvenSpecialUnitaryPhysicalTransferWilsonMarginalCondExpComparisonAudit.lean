import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The old physical-descent interface is substantially stronger than a mere
carrier realization. For every color it forces the feature analysis to kill
the corresponding physical residual.

This audit theorem is useful when deciding whether a proposed concrete
`WilsonMarginalCondExpComparisonData` can exist: exact color intertwining with
a coarser projection fixed by that color implies `A (x - P_c x) = 0`. -/
theorem WilsonMarginalCondExpComparisonData.analysis_residual_eq_zero
    {G H C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    [Fintype C]
    (P : C → G →L[ℝ] G)
    (A : G →L[ℝ] H)
    (D : WilsonMarginalCondExpComparisonData P A)
    (c : C)
    (x : G) :
    A (x - P c x) = 0 := by
  let u : G := x - P c x
  let y : D.Marginal := D.lift x
  let q : D.Marginal := D.marginalCondExp (D.lift u)
  have hliftResidual : D.lift u = y - D.marginalColor c y := by
    dsimp [u, y]
    rw [map_sub, D.lift_color_intertwining]
  have hqfixed : D.marginalColor c q = q := by
    simpa [q] using D.coarse_fixed_by_color c u
  have horth : inner ℝ (D.lift u) q = 0 := by
    rw [hliftResidual, inner_sub_left]
    have hs := D.color_symmetric c y q
    rw [hqfixed] at hs
    exact sub_eq_zero.mpr hs.symm
  have hQq : D.marginalCondExp q = q := by
    have h := congrArg
      (fun R : D.Marginal →L[ℝ] D.Marginal => R (D.lift u))
      D.coarse_idempotent
    simpa [q] using h
  have hinner : inner ℝ (D.lift u) q = inner ℝ q q := by
    have hs := D.coarse_symmetric (D.lift u) q
    rw [hQq] at hs
    simpa [q] using hs.symm
  have hqnorm : ‖q‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← hinner, horth]
  have hAuSq : ‖A u‖ ^ 2 = 0 := by
    rw [← D.coarse_norm_sq u]
    simpa [q] using hqnorm
  have hAu : ‖A u‖ = 0 := by
    nlinarith [norm_nonneg (A u)]
  exact norm_eq_zero.mp hAu

/-- Equivalently, every color operator admitted by the old exact-descent
interface is invisible to the analysis map: `A (P_c x) = A x`. -/
theorem WilsonMarginalCondExpComparisonData.analysis_color_eq
    {G H C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    [Fintype C]
    (P : C → G →L[ℝ] G)
    (A : G →L[ℝ] H)
    (D : WilsonMarginalCondExpComparisonData P A)
    (c : C)
    (x : G) :
    A (P c x) = A x := by
  have hzero := D.analysis_residual_eq_zero P A c x
  have hmap : A (x - P c x) = A x - A (P c x) := by
    rw [map_sub]
  rw [hmap] at hzero
  exact (sub_eq_zero.mp hzero).symm

end

end MathlibAnalytic
end MGAP4D
