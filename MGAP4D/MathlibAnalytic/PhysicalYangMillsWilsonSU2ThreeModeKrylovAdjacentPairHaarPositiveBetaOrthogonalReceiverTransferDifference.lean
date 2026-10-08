import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaOrthogonalReceiverExact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalUnregularizedRetainedL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPosteriorProjectionNormLoss
import Mathlib.Tactic

/-!
# P4-Q2: genuine positive-beta constant-orthogonal receiver transfer variation

For an ORIGINAL physical input f orthogonal to the physical constant unit,
the beta-zero normalized physical transfer annihilates f exactly.
Consequently the TRUE positive-beta pair-Haar receiver is controlled by
the actual finite-volume operator difference S_beta - S_0, including the
required extra inverse physical transfer norm lambda_beta^(-1).

The original transported positive-beta conditional expectations are
unchanged. Their exact orthogonal-projection Pythagoras identity yields

  A_beta(f) = (# spatial links) * ||V_beta f||^2
                - sum_e ||Q_beta,e (V_beta f)||^2
             <= (# spatial links) *
                (lambda_beta^(-1) * ||S_beta - S_0|| * ||f||)^2.

The resulting genuine physical Rayleigh estimate has coefficient ONE
on the constant-orthogonal combined sector, not a factor two.
The operator-difference norm depends on beta and finite spatial H;
no unproved bound linear in beta, volume-uniform estimate, Dobrushin
hypothesis or continuum Yang--Mills mass gap is inserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q2DiffTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2DiffCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2DiffSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2DiffMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2DiffBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2DiffLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine normalized physical transfer at positive beta minus its
exact beta-zero rank-one reference; both operators act on the original
physical gauge-invariant Haar Hilbert space. -/
noncomputable def physicalNormalizedTransferBetaZeroDifference
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta -
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN 0 (by norm_num)

/-- The actual beta-zero normalized transfer annihilates every input
orthogonal to the constant physical unit; this is the established
physical beta-zero rank-one theorem, not a substitute kernel. -/
theorem physicalNormalizedTransfer_zero_of_constantOrthogonal
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN 0 (by norm_num) f = 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_eq_rankOne
    H N hN, InnerProductSpace.rankOne_apply, horth]
  simp

/-- The exact norm of the ORIGINAL normalized physical pair-Haar receiver:
the joint-half-density isometry cancels, but the original inverse
physical transfer normalization must remain. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_norm_eq_inv_transferNorm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖ := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  have hEq :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_eq_pairHaarReceiver
      H N hN beta hbeta f
  have hNorm :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_norm_eq_inv_transferNorm
      H N hN beta hbeta f
  calc
    ‖v‖ = ‖U v‖ := (U.norm_map _).symm
    _ = ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖ := by
      rw [← hEq]
      exact hNorm

/-- P4-Q2 operator-variation estimate on the TRUE positive-beta
receiver, vanishing with S_beta - S_0 for constant-orthogonal inputs.
The inverse top transfer norm remains explicit and volume dependent. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_orthogonal_norm_le_transferDifference
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
      (‖physicalNormalizedTransferBetaZeroDifference H N hN beta hbeta‖ * ‖f‖) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S₀ := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let D := physicalNormalizedTransferBetaZeroDifference H N hN beta hbeta
  let a : ℝ := ‖T‖⁻¹
  have hS₀ : S₀ f = 0 :=
    physicalNormalizedTransfer_zero_of_constantOrthogonal H N hN f horth
  have hD : D f = S f := by
    change S f - S₀ f = S f
    rw [hS₀, sub_zero]
  have hOp : ‖D f‖ ≤ ‖D‖ * ‖f‖ := ContinuousLinearMap.le_opNorm D f
  have ha : 0 ≤ a := inv_nonneg.mpr (norm_nonneg T)
  have hNorm :
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
        a * ‖S f‖ :=
    normalizedPhysicalOneSlabPairHaarReceiver_norm_eq_inv_transferNorm
      H N hN beta hbeta f
  change ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ ≤
    a * (‖D‖ * ‖f‖)
  calc
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
        a * ‖S f‖ := hNorm
    _ = a * ‖D f‖ := by rw [hD]
    _ ≤ a * (‖D‖ * ‖f‖) := mul_le_mul_of_nonneg_left hOp ha

/-- P4-Q2 exact all-link Pythagorean budget in the true positive-beta
orthogonal receiver sector. The retained-projection term is preserved:
discarding it produces the crude cardinality bound below. -/
theorem physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_eq_normLoss
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta f =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ ^ 2 -
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2 := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  have hzero :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_eq_zero_of_constantOrthogonal
      H N hN f horth
  have hPyth (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖v - Q e v‖ ^ 2 = ‖v‖ ^ 2 - ‖Q e v‖ ^ 2 :=
    normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_sq_eq_normLoss
      H N hN beta hbeta f e
  simp only [physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy,
    hzero, sub_zero]
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v - Q e v‖ ^ 2) =
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (‖v‖ ^ 2 - ‖Q e v‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact hPyth e
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ‖v‖ ^ 2 -
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖Q e v‖ ^ 2 := by
      rw [Finset.sum_sub_distrib]
      simp

/-- Unconditional finite-volume P4-Q2 estimate for the genuine
orthogonal receiver drift, with the precise physical beta-transfer
perturbation parameter instead of a fictional uniform constant.
No estimate on ||S_beta-S_0|| in terms of beta or H is assumed. -/
theorem physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_transferDifference
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta f ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (‖physicalNormalizedTransferBetaZeroDifference H N hN beta hbeta‖ *
          ‖f‖)) ^ 2 := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      (‖physicalNormalizedTransferBetaZeroDifference H N hN beta hbeta‖ * ‖f‖)
  have hv : ‖v‖ ≤ c :=
    normalizedPhysicalOneSlabPairHaarReceiver_orthogonal_norm_le_transferDifference
      H N hN beta hbeta f horth
  have hvSq : ‖v‖ ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hper (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖v - Q e v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    have hp :=
      normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_sq_eq_normLoss
        H N hN beta hbeta f e
    change ‖v - Q e v‖ ^ 2 = ‖v‖ ^ 2 - ‖Q e v‖ ^ 2 at hp
    nlinarith [sq_nonneg (‖Q e v‖)]
  have hsum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖v - Q e v‖ ^ 2) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * c ^ 2 := by
    calc
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖v - Q e v‖ ^ 2) ≤
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro e _he
          exact hper e
      _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ‖v‖ ^ 2 := by simp
      _ ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          c ^ 2 := by
          exact mul_le_mul_of_nonneg_left hvSq (by positivity)
  have hzero :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_eq_zero_of_constantOrthogonal
      H N hN f horth
  simpa only [physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy,
    hzero, sub_zero] using hsum

/-- The exact orthogonal Rayleigh equality of #5292 plus the original
positive-beta transfer-variation estimate. Neither individual mode
orthogonality nor a substitute posterior is required. -/
theorem pairHaarSpatialLinkResidualGram_orthogonal_rayleigh_le_transferDifference
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
      (∑ i : ι, a i • f i) = 0) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
            H N hN beta hbeta (f i))) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (‖physicalNormalizedTransferBetaZeroDifference H N hN beta hbeta‖ *
          ‖∑ i : ι, a i • f i‖)) ^ 2 := by
  classical
  calc
    star a ⬝ᵥ
        (Matrix.mulVec
          (pairHaarSpatialLinkResidualGram H N hN beta hbeta
            (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
              H N hN beta hbeta (f i))) a) =
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
        (∑ i : ι, a i • f i) :=
      pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_eq_receiverDrift_of_combinedOrthogonal
        H N hN beta hbeta f a horth
    _ ≤ _ :=
      physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_transferDifference
        H N hN beta hbeta (∑ i : ι, a i • f i) horth

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
