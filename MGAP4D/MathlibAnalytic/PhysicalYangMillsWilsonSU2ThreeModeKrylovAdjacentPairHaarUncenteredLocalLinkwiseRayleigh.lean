import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredCoefficientL1Rayleigh
import Mathlib.Tactic

/-!
# P4-Q2: exact-original link-resolved right-Krylov Rayleigh envelope

The fully explicit #5319 bound used one worst-case finite-volume Wilson
coefficient for every spatial link.  Here the physical posterior losses
remain indexed by their ACTUAL spatial links. For the original pair-Haar
receiver vectors v_j and original transported Wilson projections Q_e, set

  d(e,j) = ‖v_j - Q_e v_j‖.

The genuine uncentered right-Krylov Gram obeys

  aᵀ G_right a ≤ ∑_e (∑_j |a_j| d(e,j))².

Unlike |Links(H)| times a global worst-case budget, this retains the
precise local conditional-expectation residuals, the complete Wilson
posterior, all correlations within each residual, and the independent
frozen beta(n) / fine beta(n+1) couplings.

A second theorem accepts rigorously certified LINK-DEPENDENT upper
bounds b(e,j) for these very residuals. This is the next interface
where geometric locality, conditional variance or covariance estimates
may genuinely remove volume dependence. We do NOT assume finite
support, summability, or a volume-uniform b here and make NO
continuum Yang--Mills mass-gap assertion. No Dobrushin, surrogate law,
sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4LocalRightTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4LocalRightCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4LocalRightSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4LocalRightMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4LocalRightBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4LocalRightLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact original Wilson-posterior residuals yield a *linkwise*
coefficient estimate of the full Gram. Unlike a global norm bound,
the triangle inequality is applied only within each original link. -/
theorem pairHaarSpatialLinkResidualGram_rayleigh_le_linkwiseCoefficientL1
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (v : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta v) a) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ i : ι, |a i| *
          ‖v i - pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN beta hbeta e (v i)‖) ^ 2 := by
  classical
  rw [pairHaarSpatialLinkResidualGram_rayleigh]
  apply Finset.sum_le_sum
  intro e _he
  have hNorm :
      ‖∑ i : ι, a i •
        (v i - pairHaarTransportedGroundStateSpatialLinkProjection
          H N hN beta hbeta e (v i))‖ ≤
        ∑ i : ι, |a i| *
          ‖v i - pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN beta hbeta e (v i)‖ := by
    apply norm_sum_le_of_le
    intro i _hi
    rw [norm_smul, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (norm_nonneg _) hNorm 2

/-- One ORIGINAL positive-beta pair-Haar link residual of an actual
uncentered fine-right Krylov mode. Frozen beta(n) defines Q_e and the
receiver; fine beta(n+1) defines the right orbit. -/
noncomputable def fineRightKrylovOriginalPosteriorLinkResidualNorm
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (j : Fin (r + 1)) : ℝ :=
  let H := halfExtent (n + 1)
  let v := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ))
  ‖v - pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e v‖

theorem fineRightKrylovOriginalPosteriorLinkResidualNorm_nonneg
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (j : Fin (r + 1)) :
    0 ≤ fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e j := by
  exact norm_nonneg _

/-- TRUE UN-CENTERED Yang--Mills right-Krylov Gram: each physical
link retains its own posterior residual budget (no |Links(H)|). -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_localLinkwiseL1
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        (∑ j : Fin (r + 1), |a j| *
          fineRightKrylovOriginalPosteriorLinkResidualNorm
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r e j) ^ 2 := by
  classical
  simpa only [fineRightKrylovPairHaarResidualGram,
    fineRightKrylovOriginalPosteriorLinkResidualNorm] using
    (pairHaarSpatialLinkResidualGram_rayleigh_le_linkwiseCoefficientL1
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (fun j : Fin (r + 1) =>
        normalizedPhysicalOneSlabPairHaarReceiver
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ))) a)

/-- A local-variance/covariance handoff with no change to the posterior.
Any verified per-link physical bound b(e,j) produces a squared link-sum
Rayleigh estimate; no hard support or volume independence is postulated. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedLocalBudgets
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (b : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)) →
      Fin (r + 1) → ℝ)
    (hb : ∀ e j,
      fineRightKrylovOriginalPosteriorLinkResidualNorm
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e j ≤ b e j) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        (∑ j : Fin (r + 1), |a j| * b e j) ^ 2 := by
  classical
  have hLocal :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_localLinkwiseL1
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  apply le_trans hLocal
  apply Finset.sum_le_sum
  intro e _he
  have hSum :
      (∑ j : Fin (r + 1), |a j| *
        fineRightKrylovOriginalPosteriorLinkResidualNorm
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e j) ≤
      ∑ j : Fin (r + 1), |a j| * b e j := by
    apply Finset.sum_le_sum
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hb e j) (abs_nonneg _)
  have hNonneg : 0 ≤
      ∑ j : Fin (r + 1), |a j| *
        fineRightKrylovOriginalPosteriorLinkResidualNorm
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e j := by
    apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (abs_nonneg _)
      (fineRightKrylovOriginalPosteriorLinkResidualNorm_nonneg
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e j)
  exact pow_le_pow_left₀ hNonneg hSum 2

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
