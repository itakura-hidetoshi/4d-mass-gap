import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroFrozenPositiveNoUniformFrame
import Mathlib.Tactic

/-!
# P4-Q2-L: explicit linear growth of the authentic normalized all-one Rayleigh witness

For genuine fine beta(n+1)=0 and positive frozen beta(n), the all-one
coefficient vector has squared norm (r+1).  The original (not proxy)
right-link Wilson posterior Gram has Rayleigh value
E_unit(beta(n),H) * (r+1)^2.  Dividing by the actual coefficient
squared norm gives the exact normalized value E_unit*(r+1).
This is a depth-quantified finite-volume obstruction, not a general
positive-fine-coupling, volume-uniform or continuum assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

/-- The actual coefficient l2 squared norm of the all-one depth vector. -/
theorem fineRightKrylov_ones_coeff_sq_norm_eq (r : ℕ) :
    (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) =
      ((r + 1 : ℕ) : ℝ) := by
  simp

/-- Exact normalized Rayleigh quotient of the original Wilson posterior
Gram grows linearly with Krylov depth in the genuine positive-frozen,
zero-fine coupling sector. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_eq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hFine : beta (n + 1) = 0) :
    (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r)
        (fun _ : Fin (r + 1) => (1 : ℝ)))) /
      (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) =
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) * ((r + 1 : ℕ) : ℝ) := by
  rw [fineRightKrylovPairHaarResidualGram_ones_rayleigh_eq_unitEnergy_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFine,
    fineRightKrylov_ones_coeff_sq_norm_eq]
  have hcard : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The normalized Rayleigh quotient is strictly positive at every depth,
with no assumed positivity of a surrogate vacuum receiver. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_pos
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hFine : beta (n + 1) = 0) (hFrozen : 0 < beta n) :
    0 <
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  rw [fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_eq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFine]
  exact mul_pos
    (physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
      (halfExtent (n + 1)) (beta n) hFrozen)
    (by positivity)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
