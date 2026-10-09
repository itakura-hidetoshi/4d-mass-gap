import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverStrictPositiveBeta
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroUniformIffUnitEnergyZero
import Mathlib.Tactic

/-!
# P4-Q2-K: actual positive frozen coupling excludes fine-zero depth-uniform right Gram frames

The P4-Q2-J theorem gives unconditional strict positivity of the ORIGINAL
physical constant-input full-right-link posterior innovation for every
finite volume at beta>0. Existing P4-Q2-F identifies the genuine
UNCENTERED fine-right Krylov original Wilson posterior Gram with the
rank-one constant unit energy when the NEXT coupling beta(n+1) is zero.

Together these imply all genuine right Gram entries are strictly positive
at frozen beta(n)>0, and a coefficient-ℓ² Rayleigh upper bound
independent of Krylov depth is impossible in the particular fine-zero
coupling sector.

The frozen and fine couplings remain DISTINCT. This is a negative
classification for a fine-zero sector, not a no-go theorem for continuum
Yang-Mills nor a positive volume-uniform gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

/-- Genuine original Wilson right-Krylov residual Gram has positive
rank-one entries at every depth when the next coupling is literally
zero and the frozen physical Wilson coupling is strictly positive. -/
theorem fineRightKrylovPairHaarResidualGram_entry_pos_of_fine_zero_frozen_pos
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hFine : beta (n + 1) = 0) (hFrozen : 0 < beta n)
    (r : ℕ) (i j : Fin (r + 1)) :
    0 <
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) i j := by
  rw [fineRightKrylovPairHaarResidualGram_entry_eq_unitEnergy_of_fine_beta_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFine i j]
  exact physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
    (halfExtent (n + 1)) (beta n) hFrozen

/-- No finite-depth original right Gram can be the zero matrix in
this specific positive-frozen/fine-zero coupling configuration. -/
theorem fineRightKrylovPairHaarResidualGram_eachDepth_ne_zero_of_fine_zero_frozen_pos
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hFine : beta (n + 1) = 0) (hFrozen : 0 < beta n)
    (r : ℕ) :
    fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r ≠ 0 := by
  intro hz
  have hEntry :
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) (0 : Fin (r + 1)) (0 : Fin (r + 1)) = 0 := by
    rw [hz]
    simp
  exact (ne_of_gt
    (fineRightKrylovPairHaarResidualGram_entry_pos_of_fine_zero_frozen_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFine hFrozen r 0 0)) hEntry

/-- There exists NO depth-independent coefficient-ℓ² Rayleigh frame
constant for the ACTUAL fine-zero original Wilson right posterior Gram
if the distinct frozen coupling is positive. This eliminates the
previously conditional E_unit>0 hypothesis using P4-Q2-J. -/
theorem fineRightKrylovPairHaarResidualGram_no_uniformRayleigh_of_fine_zero_frozen_pos
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hFine : beta (n + 1) = 0) (hFrozen : 0 < beta n) :
    ¬ ∃ C : ℝ, ∀ (r : ℕ) (a : Fin (r + 1) → ℝ),
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        C * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  intro hFrame
  have hEnergyZero :=
    (fineRightKrylovPairHaarResidualGram_allDepth_uniformRayleigh_iff_unitEnergy_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFine).mp hFrame
  exact (ne_of_gt
    (physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
      (halfExtent (n + 1)) (beta n) hFrozen)) hEnergyZero

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
