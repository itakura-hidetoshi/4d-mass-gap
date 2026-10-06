import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalVolumeUniformDobrushinCutoff
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorStrictRandomScanGeometric
import Mathlib.Tactic

/-!
# Volume-uniform canonical posterior random-scan contraction

The canonical posterior route now has a positive coupling interval, independent
of the finite volume H and rank N, on which every refined influence row is
bounded by the same scalar alphaBar(s,beta) < 1.

Pointwise random-scan variation propagation is column-oriented.  This file
therefore closes the transpose side explicitly rather than silently identifying
row and column control.

The source-centered base-L1 exponential weight is symmetric because the
periodic base-L1 distance is symmetric.  Hence the same off-diagonal reciprocal
shell majorant used for posterior rows also controls posterior columns.  The
direct local column has the same degree-18 bound by symmetry of intrinsic
spatial plaquette locality.

Consequently every actual canonical refined posterior column obeys

  sum_target c(target,source) <= alphaBar(s,beta),

with the identical H- and N-independent scalar.  For

  n_H = card(spatial links)

define the finite-volume random-scan rate

  q_H(s,beta) = (n_H - 1 + alphaBar(s,beta)) / n_H.

Then 0 <= q_H < 1 and every nonnegative pointwise variation envelope contracts
by q_H at one random-scan step and by q_H^m after m steps.

The rate still depends on H through the random-scan normalization n_H; the
strict coefficient alphaBar and its positive beta cutoff do not.  No
identification of update time with Euclidean physical time is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open Filter

noncomputable section

local instance posteriorCanonicalUniformRandomScanSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Symmetry of the source-centered base-L1 exponential weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_symm
    (H : ℕ)
    (s : ℝ)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s source target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s target source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
  apply congrArg (fun d : ℕ => s ^ d)
  unfold periodicHypercubicEdgeBaseL1Distance
  exact
    periodicHypercubicVertexL1Distance_symm
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source).1
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target).1

/-- Off-diagonal intrinsic local-neighbor membership is symmetric. -/
theorem
    periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_comm
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target ↔
      target ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H source := by
  rw [
    periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff,
    periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff]
  constructor
  · rintro ⟨hne, hlocal⟩
    exact
      ⟨Ne.symm hne,
        periodicHypercubicEvenSpatialSlicePlaquetteLocal_symm H hlocal⟩
  · rintro ⟨hne, hlocal⟩
    exact
      ⟨Ne.symm hne,
        periodicHypercubicEvenSpatialSlicePlaquetteLocal_symm H hlocal⟩

/-- The direct local part of every actual canonical refined posterior column
has the same degree-18 bound as a row. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile_columnSum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
        H beta target source) ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
  classical
  let neighbors :=
    periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H source
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
      beta
  have hq : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
        beta hbeta
  have hCard : (neighbors.card : ℝ) ≤ 18 := by
    exact_mod_cast
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors_card_le_eighteen
        H source
  have hEq :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
          H beta target source) =
        (neighbors.card : ℝ) * q := by
    change
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        if source ∈
            periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target
          then q else 0) =
        (neighbors.card : ℝ) * q
    simp_rw [
      periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_comm
        H _ source]
    rw [← Finset.sum_filter]
    have hFilter :
        (Finset.univ.filter fun target :
          PeriodicHypercubicEvenSpatialSliceLink H => target ∈ neighbors) =
          neighbors := by
      ext target
      simp
    rw [hFilter]
    simp [nsmul_eq_mul]
  rw [hEq]
  exact mul_le_mul_of_nonneg_right hCard hq

/-- Total actual response-generated remote influence mass in one posterior
column. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
      H N hN s hs beta hbeta hcut target source

/-- The reciprocal source-centered weight mass used by a posterior column is
the already-bounded off-diagonal reciprocal mass after symmetry of base-L1
distance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_sourceCenteredOffDiagonalReciprocalWeightMass_eq
    (H : ℕ)
    (s : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase source,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s source target)⁻¹) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
        H s source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
  apply Finset.sum_congr rfl
  intro target _htarget
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_symm
      H s source target]

/-- For s > 8, the actual remote posterior column mass obeys the same explicit
volume-independent scalar bound as a row. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass_le
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass
        H N hN s (by linarith) beta hbeta hcut source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s := by
  classical
  let hsOne : 1 ≤ s := by linarith
  let C :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
      s beta
  let remote :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
        H N hN s hsOne beta hbeta hcut target source
  let weight :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s source target
  have hC : 0 ≤ C := by
    dsimp [C]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor_nonneg
        H N hN s hsOne beta hbeta hcut
  have hDiag : remote source = 0 := by
    simp [remote,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile]
  have hErase :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H, remote target) =
        ∑ target ∈
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase source,
          remote target := by
    have h :=
      Finset.sum_erase_add
        (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
        (f := remote)
        (Finset.mem_univ source)
    rw [hDiag] at h
    simpa using h.symm
  have hPoint :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        remote target ≤ C * (weight target)⁻¹ := by
    intro target
    simpa [remote, C, weight, hsOne] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile_le
        H N hN s hsOne beta hbeta hcut target source
  have hMass :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass_le_majorant
      H s hs source
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass
  change (∑ target : PeriodicHypercubicEvenSpatialSliceLink H, remote target) ≤ _
  rw [hErase]
  calc
    (∑ target ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase source,
        remote target) ≤
      ∑ target ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase source,
        C * (weight target)⁻¹ := by
          apply Finset.sum_le_sum
          intro target _htarget
          exact hPoint target
    _ =
      C *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s source := by
            rw [Finset.mul_sum]
            congr 1
            simpa [weight] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_sourceCenteredOffDiagonalReciprocalWeightMass_eq
                H s source
    _ ≤
      C *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s :=
      mul_le_mul_of_nonneg_left hMass hC
    _ =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s := by
            rfl

/-- Every actual canonical refined posterior column is bounded by the same
H- and N-independent coefficient that controls rows. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedColumnSum_le_uniformCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    let hsOne : 1 ≤ s := by linarith
    let R :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
        H N hN s hsOne beta hbeta hcut
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta := by
  dsimp only
  let hsOne : 1 ≤ s := by linarith
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hsOne beta hbeta hcut
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile_columnSum_le
      H beta hbeta source
  have hRemote :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass_le
      H N hN s hs beta hbeta hcut source
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source) =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
          H beta target source) +
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass
        H N hN s hsOne beta hbeta hcut source := by
          unfold
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro target _htarget
          exact
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedInfluence_eq_local_add_remote
              H N hN s hsOne beta hbeta hcut target source
    _ ≤
      18 *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
            beta +
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
            s beta *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
            s :=
      add_le_add hLocal hRemote
    _ =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta := rfl

/-- The actual strict canonical posterior Dobrushin data inherit the uniform
column bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_columnSum_le_coefficient
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
        H N hN s hs beta hbeta hbetaCutoff B).influence target source) ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
        H N hN s hs beta hbeta hbetaCutoff B).coefficient := by
  let hHalf :=
    hbetaCutoff.trans
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_le_halfBarrierCutoff
        s hs)
  let hsOne : 1 ≤ s := by linarith
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hsOne beta hbeta hHalf
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedColumnSum_le_uniformCoefficient
      H N hN s hs beta hbeta hHalf source

/-- Actual canonical posterior random-scan contraction rate.  Its strict scalar
input is volume independent; only the uniform random-scan normalization depends
on the finite volume through n_H. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
    (H : ℕ)
    (s beta : ℝ) : ℝ :=
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
      s beta
  (n - 1 + alpha) / n

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
        H s beta := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
      s beta
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnOne : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (periodicHypercubicEvenSpatialSliceLink_card_pos H)))
  have hHalf :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hbetaCutoff.trans
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_le_halfBarrierCutoff
        s hs)
  have hAlpha : 0 ≤ alpha := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient_nonneg
        H N hN s hs beta hbeta hHalf
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
  dsimp [n, alpha]
  exact div_nonneg (add_nonneg (sub_nonneg.mpr hnOne) hAlpha) hnPos.le

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_lt_one
    (H : ℕ)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
        H s beta < 1 := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
      s beta
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hAlpha : alpha < 1 := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
        s hs beta hbeta hbetaCutoff
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
  dsimp [n, alpha]
  apply (div_lt_one hnPos).2
  linarith

/-- One actual canonical posterior random-scan step contracts every
nonnegative pointwise variation envelope by the strict rate above. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanUpdatedVariation_le_rate_mul
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          H N hN s hs beta hbeta hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
          H s beta * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha : ℝ := D.coefficient
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hnOne : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hEdge))
  have hColumn :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source) ≤ alpha := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_columnSum_le_coefficient
        H N hN s hs beta hbeta hbetaCutoff B source
  have hWeighted :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target) ≤
        alpha * V := by
    calc
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * V := by
            apply Finset.sum_le_sum
            intro target _htarget
            exact
              mul_le_mul_of_nonneg_left
                (hVariationLe target)
                (D.influence_nonneg target source)
      _ =
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) * V := by
            rw [Finset.sum_mul]
      _ ≤ alpha * V :=
        mul_le_mul_of_nonneg_right hColumn hV
  have hCard :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_card_mul_eq
      D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      variation hEdge source
  have hCardBound :
      n *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation source ≤
        (n - 1 + alpha) * V := by
    calc
      n *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation source =
        (n - 1) * variation source +
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            D.influence target source * variation target := by
              simpa [n, D] using hCard
      _ ≤
        (n - 1) * V + alpha * V := by
          apply add_le_add
          · exact
              mul_le_mul_of_nonneg_left
                (hVariationLe source)
                (sub_nonneg.mpr hnOne)
          · exact hWeighted
      _ = (n - 1 + alpha) * V := by ring
  have hCardBound' :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation source * n ≤
        (n - 1 + alpha) * V := by
    simpa [mul_comm] using hCardBound
  have hDiv :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation source ≤
        ((n - 1 + alpha) * V) / n :=
    (le_div_iff₀ hnPos).2 hCardBound'
  simpa [
    D,
    alpha,
    n,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate,
    div_mul_eq_mul_div] using hDiv

/-- Every finite actual canonical posterior random-scan variation iterate
contracts by q_H^m. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_le_rate_pow_mul
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V) :
    ∀ m source,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
            H N hN s hs beta hbeta hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source ≤
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
          H s beta) ^ m * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
      H s beta
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_nonneg
        H N hN s hs beta hbeta hbetaCutoff
  intro m
  induction m with
  | zero =>
      intro source
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
      ] using hVariationLe source
  | succ m ih =>
      intro source
      let previous :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m
      have hPreviousNonneg :
          ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ previous e := by
        intro e
        dsimp [previous]
        exact
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation hVariationNonneg m e
      have hEnvelopeNonneg : 0 ≤ q ^ m * V :=
        mul_nonneg (pow_nonneg hqNonneg m) hV
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanUpdatedVariation_le_rate_mul
          H N hN s hs beta hbeta hbetaCutoff B
          previous hPreviousNonneg
          (q ^ m * V) hEnvelopeNonneg
          (fun e => by
            dsimp [previous]
            simpa [q, D] using ih e)
          source
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_succ]
      calc
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            previous source ≤
          q * (q ^ m * V) := by
            simpa [D, q] using hStep
        _ = q ^ (m + 1) * V := by
          rw [pow_succ]
          ring

/-- Powers of the actual canonical posterior random-scan rate tend to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_pow_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    Tendsto
      (fun m : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate
          H s beta) ^ m)
      atTop
      (𝓝 0) := by
  exact
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_nonneg
        H N hN s hs beta hbeta hbetaCutoff)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanRate_lt_one
        H s hs beta hbeta hbetaCutoff)

end

end MathlibAnalytic
end MGAP4D
