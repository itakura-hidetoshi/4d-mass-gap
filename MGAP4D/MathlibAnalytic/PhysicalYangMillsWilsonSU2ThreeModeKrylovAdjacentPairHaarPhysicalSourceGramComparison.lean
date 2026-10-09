import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedDiagonalCovariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInputRayleigh
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4-Q2-F: original signed right-Krylov Gram dominated by the ACTUAL source Gram

The true fine right-Krylov input is F_a = sum_j a_j R_{n,j}; its
Haar-L² Gram G_source is constructed directly from the physical
beta(n+1) orbit, without centering or replacing its constant component.

PR #5338 proves the genuine frozen beta(n) one-link Wilson posterior
innovation satisfies ||I_e(F_a)||² <= gamma_beta,H * ||F_a||².
Unlike a sum over separate modes, keeping the actual signed F_a intact
retains all cross-mode cancellation BEFORE invoking a bound.

We prove the physical finite-volume Loewner/Rayleigh comparison
  a*G_right*a <= (# genuine spatial links) * gamma_beta,H * a*G_source*a.

There is NO extra factor (r+1) from the mode count. The physical
source frame constant, the true link count and inverse transfer
normalization remain dependent on volume H and depth r until independently estimated.
A conditional source-frame bridge is provided without claiming it.

The original fine beta(n+1), frozen Wilson beta(n), signed source,
posterior and transfer norm are unchanged. No Dobrushin, substitute law,
axiom, sorry/admit, claimed uniform gap or continuum conclusion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4PhysicalSourceGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4PhysicalSourceGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4PhysicalSourceGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4PhysicalSourceGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4PhysicalSourceGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4PhysicalSourceGramLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual uncentered FINE-beta physical-source Haar Hilbert Gram.
This is NOT the posterior-residual Gram and has no fake orthogonality. -/
noncomputable def fineRightKrylovOriginalPhysicalSourceGram
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.gram ℝ (fun j : Fin (r + 1) =>
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ))

/-- Exact physical input Gram Rayleigh = norm squared of the FULL signed
fine-right Krylov sum, so all input-mode cross-correlations are retained. -/
theorem fineRightKrylovOriginalPhysicalSourceGram_rayleigh_eq_sourceNorm_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovOriginalPhysicalSourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      ‖fineRightKrylovOriginalSignedPhysicalSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a‖ ^ 2 := by
  classical
  change
    star a ⬝ᵥ (Matrix.mulVec
      (Matrix.gram ℝ (fun j : Fin (r + 1) =>
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ))) a) =
      ‖∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)‖ ^ 2
  rw [Matrix.star_dotProduct_gram_mulVec]
  exact real_inner_self_eq_norm_sq _

/-- Genuine ALL-LINK Wilson posterior Rayleigh dominated by the full
source norm; one true physical per-link innovation bound is summed only
over actual spatial links, not over the individual fine Krylov modes. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalSourceNorm
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) *
        ‖fineRightKrylovOriginalSignedPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a‖ ^ 2 := by
  classical
  let H := halfExtent (n + 1)
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let V := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hRay :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V F - Q e (V F)‖ ^ 2 := by
    simpa only [H, F, V, Q, fineRightKrylovOriginalSignedPhysicalSource] using
      (fineRightKrylovPairHaarResidualGram_rayleigh_physicalInput
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖V F - Q e (V F)‖ ^ 2 ≤ gamma * ‖F‖ ^ 2 := by
    simpa only [V, Q, gamma, physicalOriginalReceiverPosteriorInnovation] using
      (physicalOriginalReceiverPosteriorInnovation_norm_sq_le_signedHilbert
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e F)
  change star a ⬝ᵥ (Matrix.mulVec
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        gamma * ‖F‖ ^ 2
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V F - Q e (V F)‖ ^ 2 := hRay
    _ ≤ ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
        gamma * ‖F‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro e _he
      exact hOne e
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        gamma * ‖F‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Original Wilson posterior/right-Krylov Gram vs ACTUAL physical
fine-source Gram as a Rayleigh (quadratic Loewner) comparison.
No factor r+1 is inserted. All the source inner products remain
inside the same original signed physical input Gram. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalSourceGram
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)) *
      (star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovOriginalPhysicalSourceGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a)) := by
  have hBound :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalSourceNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  have hSrc :=
    fineRightKrylovOriginalPhysicalSourceGram_rayleigh_eq_sourceNorm_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) *
        ‖fineRightKrylovOriginalSignedPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a‖ ^ 2 := hBound
    _ = ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)) *
      (star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovOriginalPhysicalSourceGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a)) := by
      rw [hSrc]
      ring

/-- A certified (not assumed as true) physical source-frame coefficient
passes to the original uncentered right-Krylov Gram without an
additional factor for the number of Krylov modes. The spatial-link
factor and inverse transfer normalization remain explicit. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedPhysicalSourceFrame
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (C : ℝ)
    (hSource :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovOriginalPhysicalSourceGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        C * ∑ j : Fin (r + 1), (a j) ^ 2) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)) *
      C * ∑ j : Fin (r + 1), (a j) ^ 2 := by
  let k : ℝ :=
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
      originalWilsonPhysicalSignedInnovationHilbertCoefficient
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
  have hk : 0 ≤ k :=
    mul_nonneg (Nat.cast_nonneg _)
      (originalWilsonPhysicalSignedInnovationHilbertCoefficient_nonneg
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
  have hPhysical :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalSourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      k * C * ∑ j : Fin (r + 1), (a j) ^ 2
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      k * (star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovOriginalPhysicalSourceGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a)) := hPhysical
    _ ≤ k * (C * ∑ j : Fin (r + 1), (a j) ^ 2) :=
      mul_le_mul_of_nonneg_left hSource hk
    _ = k * C * ∑ j : Fin (r + 1), (a j) ^ 2 := by ring

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
