import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalFixedRightResponseBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairPinFreeOffDiagonalShellRow
import Mathlib.Tactic

/-!
# Actual posterior canonical response to a volume-uniform Dobrushin row bound

PR #5194 constructs an actual ordinary posterior remote-response matrix with

  epsilon(target,source)
    = Mbar(s,beta) / W_source(target),

where the source-centered base-L1 exponential weight is

  W_source(target) = s ^ d_baseL1(source,target).

For s > 8, the existing three-dimensional spatial shell theorem gives the
volume-independent off-diagonal reciprocal-weight bound

  sum_{source != target} W_source(target)^(-1)
    <= 2 + 81 * (8/s) / (1 - 8/s).

This file combines that geometry with the response-to-influence linearization
from PR #5192.  The actual remote posterior influence row is bounded by

  [2 Mbar(s,beta) / exp(-8 beta)] * shellMassBar(s),

and hence every literal refined posterior row is bounded by

  18 * q_local(beta)
    + [2 Mbar(s,beta) / exp(-8 beta)] * shellMassBar(s).

The scalar on the right is independent of H and N.  If it is below one, the
actual posterior one-link conditional laws therefore form strict Dobrushin
data.  The subsequent scalar task is to choose a positive beta interval on
which this explicit coefficient is < 1.

No heat-bath-time / Euclidean-time identification, H1-D5 exact descent, or
complete Yang--Mills mass-gap claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorCanonicalUniformDobrushinSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact epsilon field of the actual canonical posterior response data. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData_epsilon
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
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut).epsilon target source =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target := by
  rfl

/-- Volume-independent prefactor after linearizing ordinary posterior response
into remote posterior influence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
    (s beta : ℝ) : ℝ :=
  2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s beta /
    Real.exp (-8 * beta)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
        s beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap_nonneg
        H N hN s hs beta hbeta hcut))
    (Real.exp_pos _).le

/-- Actual remote part of the canonical refined posterior influence row. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
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
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut
  exact if source = target then 0
    else if periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source then 0
    else
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta (R.epsilon target source)

/-- Pointwise actual remote influence inherits the reciprocal base-L1
exponential weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile_le
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
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
        H N hN s hs beta hbeta hcut target source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
          s beta *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target)⁻¹ := by
  classical
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source target
  have hPrefactor :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
          s beta :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor_nonneg
      H N hN s hs beta hbeta hcut
  have hWPos : 0 < W := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
        H s (zero_lt_one.trans_le hs) source target
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
  dsimp only
  by_cases hdiag : source = target
  · simp only [hdiag, if_true]
    exact mul_nonneg hPrefactor (inv_nonneg.mpr hWPos.le)
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp only [hlocal, if_true]
      exact mul_nonneg hPrefactor (inv_nonneg.mpr hWPos.le)
    · simp only [hlocal, if_false]
      have hLinear :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_le_two_mul_div_exp_neg_eight
          beta (R.epsilon target source)
          (R.epsilon_nonneg target source)
      calc
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
            beta (R.epsilon target source) ≤
          2 * R.epsilon target source / Real.exp (-8 * beta) :=
            hLinear
        _ =
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
              s beta *
            W⁻¹ := by
              rw [
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData_epsilon
                  H N hN s hs beta hbeta hcut target source]
              unfold
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
              dsimp [W]
              field_simp [Real.exp_ne_zero,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
                  H s (zero_lt_one.trans_le hs) source target |>.ne']
              <;> ring
        _ =
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
              s beta *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s source target)⁻¹ := by
                rfl

/-- Total actual remote influence mass in one posterior row. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteRowMass
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
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
      H N hN s hs beta hbeta hcut target source

/-- For s > 8, the actual remote posterior row mass is bounded by an explicit
volume-independent scalar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteRowMass_le
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
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteRowMass
        H N hN s (by linarith) beta hbeta hcut target ≤
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
    fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
        H N hN s hsOne beta hbeta hcut target source
  let weight :=
    fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s source target
  have hC : 0 ≤ C := by
    dsimp [C]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor_nonneg
        H N hN s hsOne beta hbeta hcut
  have hDiag : remote target = 0 := by
    simp [remote,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile]
  have hErase :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H, remote source) =
        ∑ source ∈
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
          remote source := by
    have h :=
      Finset.sum_erase_add
        (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
        (f := remote)
        (Finset.mem_univ target)
    rw [hDiag] at h
    simpa using h.symm
  have hPoint :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        remote source ≤ C * (weight source)⁻¹ := by
    intro source
    simpa [remote, C, weight, hsOne] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile_le
        H N hN s hsOne beta hbeta hcut target source
  have hMass :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass_le_majorant
      H s hs target
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteRowMass
  change (∑ source : PeriodicHypercubicEvenSpatialSliceLink H, remote source) ≤ _
  rw [hErase]
  calc
    (∑ source ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
        remote source) ≤
      ∑ source ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
        C * (weight source)⁻¹ := by
          apply Finset.sum_le_sum
          intro source hsource
          exact hPoint source
    _ =
      C *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s target := by
            simp [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass,
              weight,
              Finset.mul_sum]
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

/-- Direct local part of one actual canonical refined posterior row. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source ∈
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target then
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
      beta
  else 0

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile_sum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
        H beta target source) ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
  classical
  let neighbors :=
    periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target
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
        H target
  have hEq :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
          H beta target source) =
        (neighbors.card : ℝ) * q := by
    change
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        if source ∈ neighbors then q else 0) =
        (neighbors.card : ℝ) * q
    rw [← Finset.sum_filter]
    have hFilter :
        (Finset.univ.filter fun source :
          PeriodicHypercubicEvenSpatialSliceLink H => source ∈ neighbors) =
          neighbors := by
      ext source
      simp
    rw [hFilter]
    simp [nsmul_eq_mul]
  rw [hEq]
  exact mul_le_mul_of_nonneg_right hCard hq

/-- The actual canonical refined influence splits pointwise into its direct
local and response-generated remote parts. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedInfluence_eq_local_add_remote
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
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    let R :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
        H N hN s hs beta hbeta hcut
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
          H beta target source +
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile
          H N hN s hs beta hbeta hcut target source := by
  classical
  dsimp only
  by_cases hdiag : source = target
  · subst source
    simp [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile,
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors]
  · by_cases hlocal :
      periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · have hmem :
          source ∈
            periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target := by
        exact
          (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
            H target source).2 ⟨hdiag, hlocal⟩
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile,
        hdiag, hlocal, hmem]
    · have hnotmem :
          source ∉
            periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target := by
        intro hmem
        exact hlocal
          ((periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
            H target source).1 hmem).2
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile,
        hdiag, hlocal, hnotmem]

/-- Explicit volume-independent coefficient for the actual canonical posterior
refined influence matrix. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
    (s beta : ℝ) : ℝ :=
  18 *
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
        beta +
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
        s beta *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
        s

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta := by
  have hsOne : 1 ≤ s := by linarith
  have hShell :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
    have hsPos : 0 < s := by linarith
    have hq : 0 ≤ (8 : ℝ) * s⁻¹ := by positivity
    have hqLt : (8 : ℝ) * s⁻¹ < 1 := by
      simpa [div_eq_mul_inv] using (div_lt_one hsPos).2 hs
    positivity
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
        beta hbeta))
    (mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor_nonneg
        H N hN s hsOne beta hbeta hcut)
      hShell)

/-- Every actual canonical refined posterior row is bounded by the same scalar,
independently of H and N. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedRowSum_le_uniformCoefficient
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
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    let hsOne : 1 ≤ s := by linarith
    let R :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
        H N hN s hsOne beta hbeta hcut
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
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
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile_sum_le
      H beta hbeta target
  have hRemote :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteRowMass_le
      H N hN s hs beta hbeta hcut target
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source) =
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
          H beta target source) +
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteRowMass
        H N hN s hsOne beta hbeta hcut target := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro source _hsource
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

/-- Whenever the explicit H-independent canonical coefficient is below one,
the literal posterior one-link conditionals form strict Dobrushin data. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapDobrushinData
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
    (hStrict :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
      H N hN beta hbeta B := by
  let hsOne : 1 ≤ s := by linarith
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hsOne beta hbeta hcut
  let I := R.toRefinedInfluenceData B
  refine
    { toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData := I
      coefficient :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta
      coefficient_nonneg :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient_nonneg
          H N hN s hs beta hbeta hcut
      rowSum_le_coefficient := ?_
      coefficient_lt_one := hStrict }
  intro target
  dsimp [I, R]
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedRowSum_le_uniformCoefficient
      H N hN s hs beta hbeta hcut target

end

end MathlibAnalytic
end MGAP4D
