import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalPosteriorGramBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4-Q2-F: exact original Wilson fine-zero posterior uniformity classification

PR #5343 proves the ACTUAL signed uncentered Wilson right-Krylov Gram
at fine beta(n+1)=0 is the constant-entry matrix with coefficient
  E_unit = sum_e ||(1-Q_{beta(n),e}) V_{beta(n)} u_H||^2.

The frozen beta(n) is independent and remains arbitrary. E_unit is
nonnegative; its strict positivity was NOT proved by PR #5343.

Combining PR #5343's conditional positive-energy no-go with its exact
rank-one Rayleigh identity yields the definitive equivalences:

  (exists C in R, for every depth r and every real coefficient a,
       a*G_right(n,r)*a <= C * sum_j a_j^2)
       iff E_unit = 0;

  (for all r, G_right(n,r) = 0) iff E_unit = 0.

Thus positive frozen unit posterior energy, IF established from the
literal physical Wilson measure, is precisely the obstruction to
depth-uniform coefficient-l2 control in this fine-beta-zero sector.
Conversely exact unit energy zero makes the original posterior Gram
identically zero, even though the physical SOURCE Gram is all-ones.

This is a classification for this sector only, NOT a physical proof
that E_unit > 0 for all positive frozen beta. It makes no volume-
uniform or continuum Yang--Mills mass-gap claim. No Dobrushin,
surrogate posterior, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4FineZeroUniformTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FineZeroUniformCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FineZeroUniformSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FineZeroUniformMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FineZeroUniformBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- At genuine fine beta zero, all original uncentered right posterior
Gram matrices vanish exactly when the one authentic frozen physical
constant-unit receiver has zero full-link posterior innovation energy. -/
theorem fineRightKrylovPairHaarResidualGram_allDepth_zero_iff_unitEnergy_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hFine : beta (n + 1) = 0) :
    (∀ r : ℕ,
      fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r = 0) ↔
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) = 0 := by
  constructor
  · intro hZero
    have hEntry :=
      fineRightKrylovPairHaarResidualGram_entry_eq_unitEnergy_of_fine_beta_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 hFine (0 : Fin (0 + 1)) (0 : Fin (0 + 1))
    rw [hZero 0] at hEntry
    simpa using hEntry.symm
  · intro hE r
    ext i j
    rw [fineRightKrylovPairHaarResidualGram_entry_eq_unitEnergy_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFine i j, hE]
    simp

/-- Exact source-independent criterion for depth-uniform coefficient-l2
control of the ORIGINAL uncentered Wilson right posterior Gram at fine
beta zero. This theorem does not assume such a bound, or assume
physical strict positivity: it classifies when the bound can hold. -/
theorem fineRightKrylovPairHaarResidualGram_allDepth_uniformRayleigh_iff_unitEnergy_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (hFine : beta (n + 1) = 0) :
    (∃ C : ℝ, ∀ (r : ℕ) (a : Fin (r + 1) → ℝ),
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        C * (∑ j : Fin (r + 1), (a j) ^ 2)) ↔
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) = 0 := by
  let E : ℝ :=
    physicalOriginalUnitReceiverFullLinkEnergy
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  have hNonneg : 0 ≤ E :=
    physicalOriginalUnitReceiverFullLinkEnergy_nonneg
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  change (∃ C : ℝ, ∀ (r : ℕ) (a : Fin (r + 1) → ℝ),
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      C * (∑ j : Fin (r + 1), (a j) ^ 2)) ↔ E = 0
  constructor
  · rintro ⟨C, hFrame⟩
    by_contra hNonzero
    have hPos : 0 < E := by
      rcases lt_or_eq_of_le hNonneg with hPos | hEq
      · exact hPos
      · exact False.elim (hNonzero hEq.symm)
    have hNoGo :=
      fineRightKrylovPairHaarResidualGram_noUniformFrame_of_fine_beta_zero_unitEnergy_pos
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n hFine hPos
    apply hNoGo
    refine ⟨C, ?_⟩
    intro r
    exact hFrame r (fun _ : Fin (r + 1) => (1 : ℝ))
  · intro hE
    refine ⟨0, ?_⟩
    intro r a
    rw [fineRightKrylovPairHaarResidualGram_rayleigh_eq_unitEnergy_sum_sq_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFine a]
    change E * (∑ j : Fin (r + 1), a j) ^ 2 ≤
      0 * (∑ j : Fin (r + 1), (a j) ^ 2)
    rw [hE]
    simp

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
