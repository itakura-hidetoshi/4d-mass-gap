import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroNormalizedRayleighGrowth
import Mathlib.Tactic

/-!
# P4-Q2-M: unconditional authentic Wilson right-Gram nonvanishing for ANY fine beta

The true right-Krylov orbit starts with the canonical physical constant
unit at depth zero, independently of the next/fine Wilson coupling.
Consequently its ORIGINAL frozen-Wilson posterior Gram's (0,0) entry
at every finite depth is the genuine full-link physical constant
receiver energy, not a surrogate source Gram entry.

The unconditional P4-Q2-J physical positive-beta theorem therefore gives
a positive diagonal at every finite depth for ANY nonnegative fine beta,
including strictly positive fine coupling. We also extract an original
posterior link with strictly positive innovation norm for use in an
explicit finite-depth small-fine-beta stability inequality.

This does NOT claim all-one Rayleigh positivity, a positive lower
bound for all coefficient vectors, any depth-uniform bound, or the
continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4ZeroModeGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ZeroModeCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ZeroModeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ZeroModeMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ZeroModeBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ZeroModeLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The original finite Wilson Krylov seed is the ACTUAL constant
physical unit at depth zero for every fine beta, without any
beta(n+1)=0 hypothesis. -/
theorem fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) :
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 =
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent (n + 1)) 2 := by
  rfl

/-- Exact (0,0) Gram entry, with the real original Wilson frozen
posterior law and normalized-transfer receiver, for ARBITRARY
nonnegative fine coupling. -/
theorem fineRightKrylovPairHaarResidualGram_zeroZero_eq_unitEnergy_anyFineBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) (0 : Fin (r + 1)) (0 : Fin (r + 1)) =
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (k : ℕ)
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hR : R (0 : Fin (r + 1)) = u := by
    exact fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  rw [fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance]
  change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      inner ℝ (I e (R 0)) (I e (R 0))) =
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖I e u‖ ^ 2
  simp only [hR, real_inner_self_eq_norm_sq]

/-- Uniform in fine coupling (NOT in volume or Krylov depth):
the authentic (0,0) Wilson right-Gram entry is strictly positive
whenever the independent frozen coupling is positive. -/
theorem fineRightKrylovPairHaarResidualGram_zeroZero_pos_anyFineBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    0 < (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) (0 : Fin (r + 1)) (0 : Fin (r + 1)) := by
  rw [fineRightKrylovPairHaarResidualGram_zeroZero_eq_unitEnergy_anyFineBeta
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r]
  exact physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
    (halfExtent (n + 1)) (beta n) hFrozen

/-- At ANY fine coupling, the whole original posterior Gram cannot
be the zero matrix if the frozen beta is strictly positive. -/
theorem fineRightKrylovPairHaarResidualGram_ne_zero_anyFineBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r ≠ 0 := by
  intro hzero
  have hEntry :
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) (0 : Fin (r + 1)) (0 : Fin (r + 1)) = 0 := by
    rw [hzero]
    simp
  exact (ne_of_gt
    (fineRightKrylovPairHaarResidualGram_zeroZero_pos_anyFineBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen)) hEntry

/-- The genuine full physical unit-receiver posterior innovation has
a strictly positive original link norm whenever beta>0; this is the
one-link witness used for small positive fine-coupling stability. -/
theorem physicalOriginalUnitReceiver_exists_positive_link_norm_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      0 < ‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive beta (le_of_lt hbeta) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive beta (le_of_lt hbeta)
  have hPositive : 0 <
      physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive beta (le_of_lt hbeta) :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2 H beta hbeta
  by_contra hn
  push Not at hn
  have hzero (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖I e u‖ = 0 :=
    le_antisymm (hn e) (norm_nonneg _)
  have hsum :
      physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive beta (le_of_lt hbeta) = 0 := by
    change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖I e u‖ ^ 2) = 0
    simp [hzero]
  exact (ne_of_gt hPositive) hsum

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
