import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairPinFreeReciprocalWeightRow
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1PolynomialShellBound
import MGAP4D.MathlibAnalytic.FiniteExponentialShellGeometricBound
import Mathlib.Tactic

/-!
# Volume-uniform off-diagonal reciprocal-weight row geometry

PR #4837 isolates the canonical pin-free row problem as the finite reciprocal
source-centered exponential-weight mass

  S_H(s,target) = sum_source s^{-d(source,target)}.

For the row estimate the diagonal source is irrelevant because the canonical
pin-free influence kernel has zero diagonal.  This file therefore separates

  S_H = 1 + S_H^off

exactly and bounds only the off-diagonal mass.

The already-merged spatial base-L1 shell theorem gives

  card {source : d(source,target)=r} <= 3 * (2*r+1)^3

uniformly in the periodic side length H.  We use the elementary domination

  3 * (2*r+1)^3 <= 81 * 8^r.

For s > 8, the positive-radius tail is geometric with ratio 8/s, hence

  S_H^off(s,target)
    <= 2 + 81 * (8/s) / (1 - 8/s).

The leading 2 is exact at the level of this shell bound: the distance-zero
shell has at most three spatial link directions, and one is the erased
diagonal source.

This yields a volume- and target-independent row majorant

  sum_source K_pin(target,source)
    <= q_half(s,beta) *
       (2 + 81 * (8/s) / (1 - 8/s)).

No response symmetry, source/target exchange, lattice-cardinality factor, or
new influence coefficient is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance pinFreeOffDiagonalShellRowSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Elementary exponential domination used to convert the existing cubic shell
bound into a geometric shell bound. -/
private theorem nat_succ_le_two_pow
    (r : ℕ) :
    r + 1 ≤ 2 ^ r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      calc
        r.succ + 1 ≤ 2 * (r + 1) := by omega
        _ ≤ 2 * (2 ^ r) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (r + 1) := by
          rw [pow_succ]
          ring

/-- The existing cubic spatial-link shell bound is dominated by a simple
exponential shell bound with prefactor 81 and growth 8. -/
theorem
    periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_eightyOne_mul_eight_pow
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (r : ℕ) :
    ((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
        periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) = r).card) ≤
      81 * 8 ^ r := by
  have hPoly :=
    periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_polynomial
      H target r
  have hSucc : r + 1 ≤ 2 ^ r :=
    nat_succ_le_two_pow r
  have hLinear : 2 * r + 1 ≤ 3 * (2 ^ r) := by
    calc
      2 * r + 1 ≤ 3 * (r + 1) := by omega
      _ ≤ 3 * (2 ^ r) := Nat.mul_le_mul_left 3 hSucc
  have hCube :
      (2 * r + 1) ^ 3 ≤ (3 * (2 ^ r)) ^ 3 :=
    Nat.pow_le_pow_left hLinear 3
  calc
    ((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
        periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) = r).card) ≤
      3 * (2 * r + 1) ^ 3 := hPoly
    _ ≤ 3 * (3 * (2 ^ r)) ^ 3 :=
      Nat.mul_le_mul_left 3 hCube
    _ = 81 * 8 ^ r := by
      have hPow : (2 ^ r) ^ 3 = 8 ^ r := by
        calc
          (2 ^ r) ^ 3 = 2 ^ (r * 3) := by
            rw [← pow_mul]
          _ = 2 ^ (3 * r) := by
            rw [Nat.mul_comm]
          _ = (2 ^ 3) ^ r := by
            rw [pow_mul]
          _ = 8 ^ r := by norm_num
      rw [mul_pow, hPow]
      norm_num
      ring

/-- Positive-radius geometric tail majorant used below. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
    (s : ℝ) : ℝ :=
  81 * ((8 : ℝ) * s⁻¹) *
    (1 / (1 - (8 : ℝ) * s⁻¹))

/-- Uniform off-diagonal reciprocal-mass majorant. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
    (s : ℝ) : ℝ :=
  2 +
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
      s

/-- Reciprocal mass with the diagonal source removed. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
    (H : ℕ)
    (s : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source ∈
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source target)⁻¹

/-- Total reciprocal mass is exactly one diagonal unit plus the off-diagonal
mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass_eq_offDiagonal_add_one
    (H : ℕ)
    (s : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass
        H s target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
        H s target + 1 := by
  classical
  have hSplit :=
    Finset.sum_erase_add
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (f := fun source =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target)⁻¹)
      (Finset.mem_univ target)
  have hSelf :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target target = 1 := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self
        H s target
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
  simpa [hSelf] using hSplit.symm

/-- The total reciprocal mass has a volume-independent shell bound for s > 8. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass_le_three_add_positiveTailMajorant
    (H : ℕ)
    (s : ℝ) (hs : 8 < s)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass
        H s target ≤
      3 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
          s := by
  classical
  let distance : PeriodicHypercubicEvenSpatialSliceLink H → ℕ :=
    fun source =>
      periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
  let maxDist : ℕ := Finset.univ.sup distance
  let radius : ℕ := maxDist + 1
  let q : ℝ := (8 : ℝ) * s⁻¹
  have hsPos : 0 < s := by linarith
  have hInvNonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hsPos.le
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqLtOne : q < 1 := by
    dsimp [q]
    simpa [div_eq_mul_inv] using (div_lt_one hsPos).2 hs
  have hDistance :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        distance source < radius := by
    intro source
    have hLe : distance source ≤ maxDist := by
      dsimp [maxDist]
      exact
        Finset.le_sup
          (f := distance)
          (Finset.mem_univ source)
    dsimp [radius]
    omega
  have hShellEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass
          H s target =
        ∑ r ∈ Finset.range radius,
          (((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
              distance source = r).card : ℕ) : ℝ) *
            (s⁻¹) ^ r := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass_eq_sum_inv_pow_baseL1Distance]
    simpa [distance] using
      (FiniteDistanceShellGeometricSum.sum_pow_distance_eq_shell_sum
        distance radius hDistance (s⁻¹))
  rw [hShellEq]
  have hRadius : radius = maxDist + 1 := rfl
  rw [hRadius, Finset.sum_range_succ']
  apply add_le_add
  · have hZeroNat :=
      periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_polynomial
        H target 0
    have hZeroReal :
        (((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
            distance source = 0).card : ℕ) : ℝ) ≤ 3 := by
      have hZeroNat' :
          ((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
              distance source = 0).card) ≤ 3 := by
        simpa [distance] using hZeroNat
      exact_mod_cast hZeroNat'
    simpa using hZeroReal
  · calc
      (∑ k ∈ Finset.range maxDist,
        (((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
            distance source = k + 1).card : ℕ) : ℝ) *
          (s⁻¹) ^ (k + 1)) ≤
        ∑ k ∈ Finset.range maxDist,
          81 * q ^ (k + 1) := by
            apply Finset.sum_le_sum
            intro k hk
            have hShellNat :=
              periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_eightyOne_mul_eight_pow
                H target (k + 1)
            have hShellReal :
                (((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
                    distance source = k + 1).card : ℕ) : ℝ) ≤
                  81 * (8 : ℝ) ^ (k + 1) := by
              have hShellNat' :
                  ((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
                      distance source = k + 1).card) ≤
                    81 * 8 ^ (k + 1) := by
                simpa [distance] using hShellNat
              exact_mod_cast hShellNat'
            calc
              (((Finset.univ.filter fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
                  distance source = k + 1).card : ℕ) : ℝ) *
                    (s⁻¹) ^ (k + 1) ≤
                (81 * (8 : ℝ) ^ (k + 1)) * (s⁻¹) ^ (k + 1) :=
                  mul_le_mul_of_nonneg_right hShellReal
                    (pow_nonneg hInvNonneg _)
              _ = 81 * q ^ (k + 1) := by
                dsimp [q]
                rw [mul_pow]
                ring
      _ =
        (81 * q) *
          ∑ k ∈ Finset.range maxDist, q ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_succ]
            ring
      _ ≤
        (81 * q) * (1 / (1 - q)) := by
          exact
            mul_le_mul_of_nonneg_left
              (FiniteDistanceShellGeometricSum.sum_range_pow_le_one_div_one_sub
                q hqNonneg hqLtOne maxDist)
              (mul_nonneg (by norm_num) hqNonneg)
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
          s := by
            rfl


/-- Removing the diagonal improves the leading shell constant from three to
two. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass_le_majorant
    (H : ℕ)
    (s : ℝ) (hs : 8 < s)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
        H s target ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
        s := by
  have hTotal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass_le_three_add_positiveTailMajorant
      H s hs target
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightMass_eq_offDiagonal_add_one
      H s target] at hTotal
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
  linarith

/-- The pin-free kernel row sum uses only the off-diagonal reciprocal mass,
because the influence diagonal is exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_halfBarrier_mul_offDiagonalReciprocalWeightMass
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s target := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hDiag : K.influence target target = 0 :=
    K.influence_diagonal_zero target
  have hSplit :=
    Finset.sum_erase_add
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (f := fun source => K.influence target source)
      (Finset.mem_univ target)
  have hSumErase :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source) =
      ∑ source ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
        K.influence target source := by
    simpa [hDiag] using hSplit.symm
  rw [hSumErase]
  calc
    (∑ source ∈
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
      K.influence target source) ≤
      ∑ source ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
        q *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s source target)⁻¹ := by
          apply Finset.sum_le_sum
          intro source hsource
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_le_halfBarrier_mul_inv_sourceWeight
              H N hN s (by linarith) beta hbeta hcut target source
    _ =
      q *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s target := by
            unfold
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
            rw [Finset.mul_sum]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s target := by
            rfl

/-- Volume-uniform row majorant obtained by combining the off-diagonal
reciprocal mass with the half-barrier coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_uniformOffDiagonalShellMajorant
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hqNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hHalfCut).1
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_halfBarrier_mul_offDiagonalReciprocalWeightMass
      H N hN s hs beta hbeta hcut target).trans
      (mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass_le_majorant
          H s hs target)
        hqNonneg)

/-- Once the explicit scalar row majorant is below one, the pin-free row is
strictly contractive uniformly in H and target. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_lt_one_of_uniformOffDiagonalShellMajorant_lt_one
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (hScalar :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s < 1)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source) < 1 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_uniformOffDiagonalShellMajorant
      H N hN s hs beta hbeta hcut target).trans_lt hScalar

end

end MGAP4D.MathlibAnalytic
