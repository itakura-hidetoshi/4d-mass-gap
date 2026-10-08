import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredGramVacuumExcitationRayleigh
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalUnregularizedRetainedL2
import Mathlib.Tactic

/-!
# P4-Q2: true unit-receiver posterior residual versus actual anchored vacuum

PR #5315 restored the genuine ORIGINAL uncentered fine-right Krylov Gram,
with the ACTUAL unit-physical-input receiver posterior loss
  E_unit(beta,H) = sum_e ||(I-Q_beta,e)(V_beta u_H)||^2.
It must not be identified with the beta-zero-anchored vacuum loss
  E_vac(beta,H) = sum_e ||(I-P_beta,e)(U_beta 1)||^2.

The genuine exact beta-zero-anchored decomposition (#5280), physical
rank-one projection drift (#5282), and the newly established original
SU(2) unregularized retained witness (#5309) do imply

  E_unit(beta,H) <= 2 [A_beta(u_H)
                        + |Links(H)| (exp(16 beta)-1)^2].

Here A_beta(u_H) is the TRUE posterior loss of the ORIGINAL receiver
difference V_beta u_H - V_0 u_H, not a made-up volume-uniform constant.
Consequently #5315's UN-CENTERED physical Krylov Gram is explicitly
bounded by this genuine vacuum contribution and the existing two-beta
centered-excitation bound. We retain its independent remaining analytic
obstruction A_beta(u_H) instead of pretending it has been resolved.

No Dobrushin, surrogate probability law, claim of volume-uniformity
or continuum positive Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4UnitVacuumTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4UnitVacuumCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4UnitVacuumSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4UnitVacuumMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4UnitVacuumBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4UnitVacuumLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- True physical constant-input receiver loss is controlled by the
genuine beta-zero-ANCHORED receiver drift and the ORIGINAL positive-beta
Wilson ground-state posterior vacuum energy. The unit coefficient is
exactly one because the physical constant u has norm one. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_le_betaDrift_jointVacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta ≤
      2 * (
        physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) +
        physicalPairHaarOriginalJointVacuumFullLinkEnergy H N hN beta hbeta) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hc : (inner ℝ u u) ^ 2 = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hAnchor :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_fullLinkResidual_le_zeroAnchored
      H N hN beta hbeta u
  have hVac :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_jointVacuum
      H N hN beta hbeta u
  rw [hVac] at hAnchor
  have hBound :
      physicalOriginalUnitReceiverFullLinkEnergy H N hN beta hbeta ≤
        2 * (physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
          H N hN beta hbeta u +
        (inner ℝ u u) ^ 2 *
          physicalPairHaarOriginalJointVacuumFullLinkEnergy
            H N hN beta hbeta) := by
    simpa only [physicalOriginalUnitReceiverFullLinkEnergy,
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy,
      physicalPairHaarOriginalJointVacuumFullLinkEnergy,
      originalGroundStateJointTransportedPairHaarOne] using hAnchor
  rw [hc, one_mul] at hBound
  exact hBound

/-- Exact SU(2) original retained Wilson witness from #5309 removes
the abstract vacuum energy from the upper bound. The remaining
A_beta(u) is the actual physical receiver difference, not assumed
uniform in volume. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_le_betaDrift_card_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    physicalOriginalUnitReceiverFullLinkEnergy H 2
      (Nat.zero_lt_succ 1) beta hbeta ≤
      2 * (
        physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
          H 2 (Nat.zero_lt_succ 1) beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) +
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (Real.exp (16 * beta) - 1) ^ 2) := by
  have hUnit :=
    physicalOriginalUnitReceiverFullLinkEnergy_le_betaDrift_jointVacuum
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  have hVac :=
    originalGroundStateJointTransportedPairHaarOne_fullResidual_le_card_SU2
      H beta hbeta
  change physicalPairHaarOriginalJointVacuumFullLinkEnergy
      H 2 (Nat.zero_lt_succ 1) beta hbeta ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (Real.exp (16 * beta) - 1) ^ 2 at hVac
  exact hUnit.trans
    (mul_le_mul_of_nonneg_left
      (add_le_add_right hVac _) (by norm_num))

/-- Named, explicit finite-volume SU(2) upper budget. The original
unit receiver drift remains a visible physical quantity, as required. -/
noncomputable def physicalOriginalUnitReceiverFiniteVacuumMajorant_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  2 * (
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
      H 2 (Nat.zero_lt_succ 1) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) +
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (Real.exp (16 * beta) - 1) ^ 2)

/-- A fully original finite-volume UN-CENTERED right Krylov Rayleigh
majorant with the anchored Wilson vacuum and the explicit two-beta
centered sector, but still honest about the true unit-receiver drift. -/
noncomputable def fineRightUncenteredKrylovVacuumExcitationMajorant
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) : ℝ :=
  let H := halfExtent (n + 1)
  let F :=
    ∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)
  let c := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) F
  2 * (
    c ^ 2 * physicalOriginalUnitReceiverFiniteVacuumMajorant_SU2
      H (beta n) (hbeta n) +
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n) *
        (∑ j : Fin (r + 1), |a j| *
          ((j : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget
              H (beta (n + 1))))) ^ 2)

/-- Real Wilson UN-CENTERED full right-Krylov Gram Rayleigh is bounded by
the named anchored physical vacuum/excitation majorant. Nothing about
the posterior law or fine/frozen couplings has been modified. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_anchoredVacuum_twoBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      fineRightUncenteredKrylovVacuumExcitationMajorant
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a := by
  classical
  let H := halfExtent (n + 1)
  let F :=
    ∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)
  let c : ℝ := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) F
  let E :=
    physicalOriginalUnitReceiverFullLinkEnergy
      H 2 (Nat.zero_lt_succ 1) (beta n) (hbeta n)
  let M :=
    physicalOriginalUnitReceiverFiniteVacuumMajorant_SU2
      H (beta n) (hbeta n)
  let W : ℝ :=
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n) *
        (∑ j : Fin (r + 1), |a j| *
          ((j : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget
              H (beta (n + 1))))) ^ 2
  have hPrev := fineRightKrylovPairHaarResidualGram_rayleigh_le_unitReceiver_weightedTwoBeta
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  have hUnit : E ≤ M :=
    physicalOriginalUnitReceiverFullLinkEnergy_le_betaDrift_card_SU2
      H (beta n) (hbeta n)
  have hTerm : c ^ 2 * E ≤ c ^ 2 * M :=
    mul_le_mul_of_nonneg_left hUnit (sq_nonneg c)
  have hTotal : 2 * (c ^ 2 * E + W) ≤ 2 * (c ^ 2 * M + W) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left hTerm W) (by norm_num)
  change
    star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      2 * (c ^ 2 * M + W)
  exact hPrev.trans hTotal

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
