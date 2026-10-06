import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalVolumeUniformDobrushinCutoff
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceDecay
import Mathlib.Tactic

/-!
# Volume-uniform column control for the actual canonical posterior influence

PR #5196 closes the row-oriented posterior Dobrushin coefficient uniformly in
finite volume.  The exact random-scan variation identity is transpose-oriented,
so the next required input is the matching column bound.

The response part already has the pointwise source-centered estimate

  c_remote(target,source)
    <= C(s,beta) * W_source(target)^(-1).

The periodic base-L1 distance is symmetric, hence so is the exponential weight.
Therefore the same off-diagonal reciprocal shell majorant used for rows also
bounds columns.  The direct plaquette-local carrier is symmetric as well and
has degree at most 18.

Consequently the actual canonical refined posterior matrix satisfies, for
every source,

  sum_target c(target,source) <= alpha_bar(s,beta),

with exactly the same H- and N-independent scalar alpha_bar as the row bound.
Thus the strict data from PR #5196 carry both row and column control needed by
the transpose-oriented random-scan contraction.

No random-scan time / Euclidean-time identification, continuum generator
scaling, H1-D5 exact descent, or complete Yang--Mills mass-gap claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorCanonicalUniformColumnSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The source-centered base-L1 exponential weight is symmetric in its two link
arguments. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_comm
    (H : ℕ)
    (s : ℝ)
    (a b : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s a b =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s b a := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
  rw [periodicHypercubicEdgeBaseL1Distance_comm]

/-- Actual response-generated remote influence mass in one posterior column. -/
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

/-- For s > 8, the actual remote posterior column has the same explicit
volume-independent shell bound as a row. -/
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
    let hsOne : 1 ≤ s := by linarith
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteColumnMass
        H N hN s hsOne beta hbeta hcut source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s := by
  dsimp only
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
        H s target source
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
    have h :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteInfluenceProfile_le
        H N hN s hsOne beta hbeta hcut target source
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_comm
        H s source target] at h
    simpa [remote, C, weight] using h
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
          intro target _hTarget
          exact hPoint target
    _ =
      C *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s source := by
            unfold
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
            dsimp [weight]
            rw [Finset.mul_sum]
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

/-- The direct local canonical profile has the same degree-18 bound in a
column as in a row. -/
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
  have hPoint :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
            H beta target source =
          if target ∈ neighbors then q else 0 := by
    intro target
    by_cases hmem : target ∈ neighbors
    · rcases
        (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
          H source target).1 hmem with ⟨hne, hlocal⟩
      have hlocal' :
          periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source :=
        periodicHypercubicEvenSpatialSlicePlaquetteLocal_symm H hlocal
      have hmem' :
          source ∈ periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target :=
        (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
          H target source).2 ⟨Ne.symm hne, hlocal'⟩
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile,
        hmem, hmem', q]
    · have hnotmem' :
          source ∉ periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target := by
        intro hmem'
        rcases
          (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
            H target source).1 hmem' with ⟨hne, hlocal⟩
        have hlocal' :
            periodicHypercubicEvenSpatialSlicePlaquetteLocal H source target :=
          periodicHypercubicEvenSpatialSlicePlaquetteLocal_symm H hlocal
        exact hmem
          ((periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
            H source target).2 ⟨Ne.symm hne, hlocal'⟩)
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile,
        hmem, hnotmem', q]
  have hEq :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapLocalInfluenceProfile
          H beta target source) =
        (neighbors.card : ℝ) * q := by
    simp_rw [hPoint]
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

/-- Every actual canonical refined posterior column is bounded by the same
volume-independent coefficient used for rows. -/
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
          intro target _hTarget
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

/-- The strict canonical Dobrushin data before choosing the final cutoff also
inherit the uniform column bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapDobrushinData_columnSum_le_coefficient
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
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    let D :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapDobrushinData
        H N hN s hs beta hbeta hcut hStrict B
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      D.influence target source) ≤
      D.coefficient := by
  dsimp only
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
          H N hN s (by linarith) beta hbeta hcut).epsilon
        target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapRefinedColumnSum_le_uniformCoefficient
      H N hN s hs beta hbeta hcut source

/-- On the positive cutoff from PR #5196, the selected literal posterior
Dobrushin data have the same H-independent column coefficient as their rows. -/
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
    let D :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
        H N hN s hs beta hbeta hbetaCutoff B
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      D.influence target source) ≤
      D.coefficient := by
  dsimp only
  have hHalfBarrier :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hbetaCutoff.trans
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_le_halfBarrierCutoff
        s hs)
  have hStrict :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta < 1 :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
      s hs beta hbeta hbetaCutoff
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapDobrushinData_columnSum_le_coefficient
      H N hN s hs beta hbeta hHalfBarrier hStrict B source

end

end MathlibAnalytic
end MGAP4D
