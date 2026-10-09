import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverBetaVariation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumRetainedWitnessPythagoras
import Mathlib.Tactic

/-!
# P4-Q2: real positive-beta receiver Dirichlet energy from original beta-variation

PR #5317 proves the authentic positive-beta physical constant receiver
difference, with the original signed inverse normalization and the
beta-independent pair-Haar carrier:
  ||V_beta u - V_0 u|| <= D_H(beta).

The exact original one-link posterior Q_beta,e is an orthogonal projection:
it is conjugate by U_beta to CondExpL2 for the ORIGINAL Wilson joint law.
We prove its squared residual is at most the squared norm of ANY pair-Haar
vector, using the real-Hilbert Pythagorean identity and mathlib CondExpL2.

Applied to delta_beta = V_beta u - V_0 u, this gives
  A_beta,H(u) = sum_e ||(I-Q_beta,e)delta_beta||^2
              <= |SpatialLinks(H)| D_H(beta)^2.

This closes the remaining *finite-volume* unit-receiver drift term of
#5316 and gives an entirely explicit original SU(2) positive-beta
unit-receiver full-link estimate:
  E_unit(beta,H) <= 2 |Links(H)| *
      (D_H(beta)^2 + (exp(16 beta)-1)^2).

Finally this feeds the genuine UN-CENTERED physical right-Krylov Gram
Rayleigh bound of #5315, retaining different beta(n) and beta(n+1).

All spatial-link counts and Wilson global action/floor volume dependence
are visible. No Dobrushin, replacement posterior, newly assumed positivity,
uniform-in-H estimate, spacing-scaled generator or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- The true CondExpL2 residual has norm at most the input norm:
an exact real-Hilbert orthogonality argument using the native mathlib
conditional expectation, not a surrogate Markov operator. -/
theorem realL2_condExp_residual_sq_le_norm_sq
    {α : Type*} {m : MeasurableSpace α} [m0 : MeasurableSpace α]
    {μ : Measure α} (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    ‖f - (condExpL2 (μ := μ) ℝ ℝ hm f).1‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  let p : Lp ℝ 2 μ := (condExpL2 (μ := μ) ℝ ℝ hm f).1
  have hp : AEStronglyMeasurable[m] (fun a => p a) μ :=
    aestronglyMeasurable_condExpL2 hm f
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm f p hp
  have horth : inner ℝ (f - p) p = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hi.symm
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (f - p) p horth
  have hsum : (f - p) + p = f := by abel
  rw [hsum] at hpyth
  change ‖f - p‖ ^ 2 ≤ ‖f‖ ^ 2
  nlinarith [sq_nonneg (‖p‖)]

local instance p4UnitDirichletTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4UnitDirichletCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4UnitDirichletSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4UnitDirichletMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4UnitDirichletBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4UnitDirichletLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every original transported positive-beta one-link posterior
residual is contractive for ANY original pair-Haar L² vector:
the native CondExpL2 contractive residual and the genuine
half-density Hilbert isometry U_beta both contribute constant one. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_residual_sq_le_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (v : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖v - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
      H N e
  have hCond :
      ‖U v - P (U v)‖ ^ 2 ≤ ‖U v‖ ^ 2 := by
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply] using
      (realL2_condExp_residual_sq_le_norm_sq hm (U v))
  calc
    ‖v - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e v‖ ^ 2 =
      ‖U v - P (U v)‖ ^ 2 := by
        exact pairHaarTransportedGroundStateSpatialLinkProjection_residual_sq_eq_jointCondExp
          H N hN beta hbeta e v
    _ ≤ ‖U v‖ ^ 2 := hCond
    _ = ‖v‖ ^ 2 := by rw [U.norm_map]

/-- The EXACT anchored positive-beta receiver drift energy for the
physical constant Haar mode has an explicit finite-H beta-squared
upper bound from #5317, with no posterior-factorization hypothesis.
The loss per original right link is at most the squared receiver
difference norm, hence summing preserves the true link cardinality. -/
theorem physicalPairHaarReceiverBetaZeroDrift_unit_le_card_variation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) ≤
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalUnitReceiverBetaVariationBudget H beta) ^ 2 := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let delta :=
    normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) u
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  let D := physicalOriginalUnitReceiverBetaVariationBudget H beta
  have hDelta : ‖delta‖ ≤ D := by
    simpa only [delta, u, D] using
      (normalizedPhysicalOneSlabPairHaarReceiver_unit_sub_zero_norm_le_explicitBeta
        H N hN beta hbeta)
  have hSq : ‖delta‖ ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hDelta 2
  change
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖delta - Q e delta‖ ^ 2) ≤
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * D ^ 2
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖delta - Q e delta‖ ^ 2) ≤
      ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H, ‖delta‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro e _he
        exact pairHaarTransportedGroundStateSpatialLinkProjection_residual_sq_le_norm_sq
          H N hN beta hbeta e delta
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ‖delta‖ ^ 2 := by simp
    _ ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          D ^ 2 :=
      mul_le_mul_of_nonneg_left hSq (Nat.cast_nonneg _)

/-- Explicit finite-volume original SU(2) unit-receiver energy:
the true anchored receiver variation and the true retained Wilson
vacuum from #5309 are BOTH bounded, independently, then combined.
No volume-independent lower bound for the floor m_H(beta) is used. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_le_explicitBeta_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    physicalOriginalUnitReceiverFullLinkEnergy H 2
      (Nat.zero_lt_succ 1) beta hbeta ≤
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (2 * ((physicalOriginalUnitReceiverBetaVariationBudget H beta) ^ 2 +
        (Real.exp (16 * beta) - 1) ^ 2)) := by
  let C : ℝ :=
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let D := physicalOriginalUnitReceiverBetaVariationBudget H beta
  let X := Real.exp (16 * beta) - 1
  let A :=
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
      H 2 (Nat.zero_lt_succ 1) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  have hAnchor :
      physicalOriginalUnitReceiverFullLinkEnergy H 2
          (Nat.zero_lt_succ 1) beta hbeta ≤
        2 * (A + C * X ^ 2) := by
    simpa only [A, C, X] using
      (physicalOriginalUnitReceiverFullLinkEnergy_le_betaDrift_card_SU2
        H beta hbeta)
  have hDrift : A ≤ C * D ^ 2 := by
    simpa only [A, C, D] using
      (physicalPairHaarReceiverBetaZeroDrift_unit_le_card_variation
        H 2 (Nat.zero_lt_succ 1) beta hbeta)
  calc
    physicalOriginalUnitReceiverFullLinkEnergy H 2
        (Nat.zero_lt_succ 1) beta hbeta ≤
      2 * (A + C * X ^ 2) := hAnchor
    _ ≤ 2 * (C * D ^ 2 + C * X ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right hDrift _) (by norm_num)
    _ = C * (2 * (D ^ 2 + X ^ 2)) := by ring

/-- Name for the fully explicit actual finite-volume constant-input
receiver budget, with original β and cardinality dependencies exposed. -/
noncomputable def physicalOriginalUnitReceiverExplicitBetaMajorant_SU2
    (H : ℕ) (beta : ℝ) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
    (2 * ((physicalOriginalUnitReceiverBetaVariationBudget H beta) ^ 2 +
      (Real.exp (16 * beta) - 1) ^ 2))

/-- The TRUE UN-CENTERED fine-right Krylov Gram has an explicit
two-coupling, finite-H physical upper bound. The constant-sector
receiver and centered excitation are both quantitatively bounded,
but the remaining link/global-action/minorization volume dependence
is not eliminated by this finite-volume result. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_explicitOriginalTwoBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
    2 * (
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          (halfExtent (n + 1)) 2)
        (∑ j : Fin (r + 1), a j •
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ))) ^ 2 *
        physicalOriginalUnitReceiverExplicitBetaMajorant_SU2
          (halfExtent (n + 1)) (beta n) +
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
        (physicalOriginalOrthogonalReceiverBetaLipschitzBudget
          (halfExtent (n + 1)) (beta n) *
          (∑ j : Fin (r + 1), |a j| *
            ((j : ℝ) *
              physicalOriginalNormalizedTransferConstantStepBetaBudget
                (halfExtent (n + 1)) (beta (n + 1))))) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let F := ∑ j : Fin (r + 1), a j •
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let c : ℝ := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) F
  let E :=
    physicalOriginalUnitReceiverFullLinkEnergy
      H 2 (Nat.zero_lt_succ 1) (beta n) (hbeta n)
  let M := physicalOriginalUnitReceiverExplicitBetaMajorant_SU2 H (beta n)
  let W : ℝ :=
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n) *
        (∑ j : Fin (r + 1), |a j| *
          ((j : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget
              H (beta (n + 1))))) ^ 2
  have hPrev :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_unitReceiver_weightedTwoBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hUnit : E ≤ M := by
    simpa only [E, M, physicalOriginalUnitReceiverExplicitBetaMajorant_SU2] using
      (physicalOriginalUnitReceiverFullLinkEnergy_le_explicitBeta_SU2
        H (beta n) (hbeta n))
  have hTerm : c ^ 2 * E ≤ c ^ 2 * M :=
    mul_le_mul_of_nonneg_left hUnit (sq_nonneg c)
  have hTotal : 2 * (c ^ 2 * E + W) ≤ 2 * (c ^ 2 * M + W) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right hTerm W) (by norm_num)
  change
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      2 * (c ^ 2 * M + W)
  exact hPrev.trans hTotal

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
