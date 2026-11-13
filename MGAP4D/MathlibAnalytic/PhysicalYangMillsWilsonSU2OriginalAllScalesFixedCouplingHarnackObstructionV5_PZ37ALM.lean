import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingSchurFrameBridgeV5_PZ37ALK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALM — all-s>8 obstruction to the old uniform Schur/frame cutoff

The original, *unchanged* SU(2) Wilson fixed coupling beta0=log(3/2)/64
satisfies exp(64 beta0)=3/2 and the genuine C5 background Harnack
influence eta_R(beta0)=2/5 (kernel-certified in ALK).

The old twelve-spatial high-temperature argument admits arbitrary real
exponential weight scale s>8, not only the AKL specialization s=9.
This new leaf checks whether changing that scale evades the obstruction.

The genuine pre-existing half-barrier coefficient at fixed beta0 obeys:
 c_half(s,beta0)
   = 18*(2/5)*s^2 + exp(16 beta0)/2
   > 2304/5 > 1,  for EVERY s>8.
The pre-existing actual cutoff chain, with its exact original quantifiers
and no redefinition of any coefficient, then proves that beta0 is ABOVE
every chosen cutoff in this particular original Schur/frame family.

This rules out rescue by varying s within the *existing* sufficient
conditions. It does NOT rule out a different coercivity method at beta0,
and does NOT assert a continuum Hamiltonian gap or its absence.
One new Lean leaf only; all old physics, top, AJA, root, pins unchanged.
Append-only / tighten-only / overwrite-forbidden / same-root.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- Exact scale-uniform lower exclusion. The constant 2304/5 comes from
18*(2/5)*8^2, not a floating-point approximation. -/
theorem p4Q2PZ37ALM_allS_halfBarrier_gt_twoThousandThreeHundredFourFifths
    (s : ℝ) (hs : 8 < s) :
    (2304 / 5 : ℝ) <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta0 := by
  have hsSq : (64 : ℝ) < s ^ 2 := by
    nlinarith [sq_nonneg (s - 8)]
  have hExp : 0 < Real.exp (16 * beta0) := Real.exp_pos _
  change
    (2304 / 5 : ℝ) <
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta0 * s ^ 2 +
        Real.exp (16 * beta0) * (1 / 2 : ℝ)
  rw [p4Q2PZ37ALK_originalFixedCoupling_HarnackInfluence_eq_twoFifths]
  nlinarith

/-- Thus NO s>8 makes the unchanged half-barrier certificate true at
beta0; here the exact physical scalar is greater than one. -/
theorem p4Q2PZ37ALM_allS_halfBarrier_gt_one
    (s : ℝ) (hs : 8 < s) :
    (1 : ℝ) <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta0 := by
  have h := p4Q2PZ37ALM_allS_halfBarrier_gt_twoThousandThreeHundredFourFifths
    s hs
  linarith

/-- The original chosen half-barrier cutoff at each admissible s
is unconditionally smaller than the fixed original beta0. -/
theorem p4Q2PZ37ALM_allS_halfBarrierCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s < beta0 := by
  apply lt_of_not_ge
  intro hBetaCut
  have hBarrierSpec :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_spec
      s beta0 p4Q2PZ37ADC_fixedCoupling_pos hBetaCut).1
  exact
    (not_lt_of_ge
      (p4Q2PZ37ALM_allS_halfBarrier_gt_one s hs).le)
    hBarrierSpec

/-- The actual *strict physical sweep* selected cutoff also lies below
beta0 at every s>8, as a consequence of the unchanged cutoff chain. -/
theorem p4Q2PZ37ALM_allS_strictPhysicalSweepCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
        s < beta0 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
      s).trans_lt
      (p4Q2PZ37ALM_allS_halfBarrierCutoff_lt_original s hs)

/-- The actual pin-free shell cutoff lies below beta0. -/
theorem p4Q2PZ37ALM_allS_shellCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
        s hs < beta0 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
      s hs).trans_lt
      (p4Q2PZ37ALM_allS_strictPhysicalSweepCutoff_lt_original s hs)

/-- The actual joint leakage Schur cutoff is also excluded. -/
theorem p4Q2PZ37ALM_allS_jointSchurCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff s hs < beta0 := by
  exact
    (GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff_le_shellCutoff
      s hs).trans_lt
      (p4Q2PZ37ALM_allS_shellCutoff_lt_original s hs)

/-- The true two-boundary ordered Schur cutoff cannot reach beta0
for any allowed exponential scale. -/
theorem p4Q2PZ37ALM_allS_twoBoundarySchurCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff s hs < beta0 := by
  exact
    (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff
      s hs).trans_lt
      (p4Q2PZ37ALM_allS_jointSchurCutoff_lt_original s hs)

/-- The old two-boundary loss cutoff likewise cannot reach beta0. -/
theorem p4Q2PZ37ALM_allS_twoBoundaryLossCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
      s hs < beta0 := by
  exact
    (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
      s hs).trans_lt
      (p4Q2PZ37ALM_allS_twoBoundarySchurCutoff_lt_original s hs)

/-- The original volume-uniform twelve-spatial *frame* chosen cutoff
is too small at EVERY allowed value of s. -/
theorem p4Q2PZ37ALM_allS_frameCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
      s hs < beta0 := by
  exact
    (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff_le_twoBoundary
      s hs).trans_lt
      (p4Q2PZ37ALM_allS_twoBoundaryLossCutoff_lt_original s hs)

/-- The family of genuinely H-independent high-temperature uniform-gap
cutoffs is strictly below the unchanged original fixed coupling for
EVERY s>8, not only the s=9 specialization of AKL. -/
theorem p4Q2PZ37ALM_allS_uniformGapCutoff_lt_original
    (s : ℝ) (hs : 8 < s) :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
      s hs < beta0 := by
  exact
    (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
      s hs).trans_lt
      (p4Q2PZ37ALM_allS_frameCutoff_lt_original s hs)

/-- Exact quantifier-level exclusion: there is NO s>8 for which the
old chosen H-uniform coercivity interval contains the physical beta0.
This remains a statement about an existing SUFFICIENT route only. -/
theorem p4Q2PZ37ALM_noS_certifies_originalFixedCoupling :
    ¬ ∃ s : ℝ, ∃ hs : 8 < s,
        beta0 ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs := by
  rintro ⟨s, hs, hLe⟩
  exact (not_le_of_gt (p4Q2PZ37ALM_allS_uniformGapCutoff_lt_original s hs)) hLe

/-- Despite failure of this selected high-temperature route, ALJ's
STRICT genuine Wilson physical normalization at beta0 remains
unconditionally valid at every finite H. -/
theorem p4Q2PZ37ALM_originalFixedCoupling_trueWilsonNormalizer_strict
    (H : ℕ) :
    p4Q2PZ37AIF_originalCrossingPartition H beta0 /
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta0
          p4Q2PZ37ADC_fixedCoupling_pos.le‖ <
      Real.exp (beta0 * p4Q2PZ37AFZ_plaquetteCount H) := by
  exact
    (p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le).trans_lt
      (p4Q2PZ37ALJ_originalPartitionOverNormCeiling_lt_old
        H beta0 p4Q2PZ37ADC_fixedCoupling_pos)

/-- Explicit separation of the certified scalar proof-route obstruction
from a still-positive physical Wilson normalization result at beta0. -/
theorem p4Q2PZ37ALM_allS_routeObstruction_with_physicalWilsonBound
    (H : ℕ) :
    (¬ ∃ s : ℝ, ∃ hs : 8 < s,
      beta0 ≤ GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
        s hs) ∧
    (p4Q2PZ37AIF_originalCrossingPartition H beta0 /
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta0
          p4Q2PZ37ADC_fixedCoupling_pos.le‖ <
      Real.exp (beta0 * p4Q2PZ37AFZ_plaquetteCount H)) := by
  exact ⟨p4Q2PZ37ALM_noS_certifies_originalFixedCoupling,
    p4Q2PZ37ALM_originalFixedCoupling_trueWilsonNormalizer_strict H⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_halfBarrier_gt_twoThousandThreeHundredFourFifths
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_halfBarrier_gt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_halfBarrierCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_strictPhysicalSweepCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_shellCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_jointSchurCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_twoBoundarySchurCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_twoBoundaryLossCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_frameCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_uniformGapCutoff_lt_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_noS_certifies_originalFixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_originalFixedCoupling_trueWilsonNormalizer_strict
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALM_allS_routeObstruction_with_physicalWilsonBound
