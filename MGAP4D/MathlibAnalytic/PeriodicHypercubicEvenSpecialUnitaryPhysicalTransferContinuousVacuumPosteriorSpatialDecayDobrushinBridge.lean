import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSpatialRemoteShellSummability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFixedVolumeStrictDobrushin
import Mathlib.Tactic

/-!
# Spatial-decay to volume-uniform posterior Dobrushin bridge

PR #5190 bounds the direct local refined influence mass by
18 * q_local(beta), uniformly in the periodic side. PR #5191 proves that a
pointwise remote profile with spatial decay C * r^distance has uniformly
summable mass whenever 18 * r < 1.

This file closes the algebraic bridge between a spatially decaying ordinary
posterior response matrix and a volume-uniform refined Dobrushin row bound.

The nonlinear response-to-influence map is first linearized:

  remoteInfluence(beta, epsilon) <= 2 * epsilon / exp(-8 beta).

Hence a remote response bound

  epsilon(target,source)
    <= responsePrefactor * ratio ^ distance(target,source)

produces a remote influence bound with prefactor

  2 * responsePrefactor / exp(-8 beta).

Combining this with the degree-18 shell sum gives the row bound

  18 * q_local(beta)
    + influencePrefactor / (1 - 18 * ratio).

If this scalar is below one, the literal refined posterior influence data are
strict Dobrushin data with a coefficient independent of the volume parameter H.

This file does not prove the missing analytic spatial-decay estimate for the
actual posterior response; it identifies and packages that remaining
obligation exactly.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorSpatialDecayBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_le_two_mul_div_exp_neg_eight
    (beta epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta epsilon ≤
      2 * epsilon / Real.exp (-8 * beta) := by
  let radius : ℝ := 2 * (epsilon / Real.exp (-8 * beta))
  have hRadius : 0 ≤ radius := by
    dsimp [radius]
    exact mul_nonneg (by norm_num)
      (div_nonneg hepsilon (Real.exp_pos _).le)
  let y : ℝ := Real.exp (-radius)
  have hyPos : 0 < y := by
    dsimp [y]
    exact Real.exp_pos _
  have hyLeOne : y ≤ 1 := by
    dsimp [y]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hNum : 0 ≤ 1 - y := sub_nonneg.mpr hyLeOne
  have hDenPos : 0 < 1 + y := by linarith
  have hExpProd :
      Real.exp radius * Real.exp (-radius) = 1 := by
    rw [← Real.exp_add]
    simp
  have hRewrite :
      (Real.exp radius - 1) / (Real.exp radius + 1) =
        (1 - y) / (1 + y) := by
    dsimp [y]
    apply
      (div_eq_div_iff
        (ne_of_gt (by positivity : 0 < Real.exp radius + 1))
        (ne_of_gt (by positivity : 0 < 1 + Real.exp (-radius)))).2
    nlinarith [hExpProd]
  have hFrac :
      (1 - y) / (1 + y) ≤ 1 - y := by
    apply (div_le_iff₀ hDenPos).2
    have hProduct : 0 ≤ (1 - y) * y :=
      mul_nonneg hNum hyPos.le
    nlinarith
  have hTail : 1 - y ≤ radius := by
    dsimp [y]
    linarith [Real.one_sub_le_exp_neg radius]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
  dsimp [radius]
  rw [hRewrite]
  simpa [radius] using hFrac.trans hTail

structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    (R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta) where
  distance :
    PeriodicHypercubicEvenSpatialSliceLink H →
      PeriodicHypercubicEvenSpatialSliceLink H → ℕ
  radius : ℕ
  ratio : ℝ
  responsePrefactor : ℝ
  ratio_nonneg : 0 ≤ ratio
  responsePrefactor_nonneg : 0 ≤ responsePrefactor
  growth_mul_ratio_lt_one : 18 * ratio < 1
  distance_lt_radius :
    ∀ target source, distance target source < radius
  reachable :
    ∀ target source,
      source ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
          H (distance target source) target
  remote_epsilon_le :
    ∀ target source,
      source ≠ target →
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source →
      R.epsilon target source ≤
        responsePrefactor * ratio ^ distance target source

namespace
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData

noncomputable def influencePrefactor
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R) : ℝ :=
  2 * D.responsePrefactor / Real.exp (-8 * beta)

theorem influencePrefactor_nonneg
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R) :
    0 ≤ D.influencePrefactor := by
  unfold influencePrefactor
  exact div_nonneg
    (mul_nonneg (by norm_num) D.responsePrefactor_nonneg)
    (Real.exp_pos _).le

noncomputable def remoteInfluenceProfile
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (_D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source = target then 0
    else if periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source then 0
    else
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta (R.epsilon target source)

theorem remoteInfluenceProfile_le
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    D.remoteInfluenceProfile target source ≤
      D.influencePrefactor *
        D.ratio ^ D.distance target source := by
  classical
  unfold remoteInfluenceProfile
  by_cases hdiag : source = target
  · simp only [hdiag, if_true]
    exact
      mul_nonneg D.influencePrefactor_nonneg
        (pow_nonneg D.ratio_nonneg _)
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp only [hlocal, if_true]
      exact
        mul_nonneg D.influencePrefactor_nonneg
          (pow_nonneg D.ratio_nonneg _)
    · simp only [hlocal, if_false]
      have hLinear :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_le_two_mul_div_exp_neg_eight
          beta (R.epsilon target source)
          (R.epsilon_nonneg target source)
      have hResponse :=
        D.remote_epsilon_le target source hdiag hlocal
      have hFloorPos : 0 < Real.exp (-8 * beta) := Real.exp_pos _
      calc
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
            beta (R.epsilon target source) ≤
          2 * R.epsilon target source / Real.exp (-8 * beta) :=
            hLinear
        _ ≤
          2 *
              (D.responsePrefactor *
                D.ratio ^ D.distance target source) /
            Real.exp (-8 * beta) := by
              exact
                (div_le_div_iff_of_pos_right hFloorPos).2
                  (mul_le_mul_of_nonneg_left hResponse (by norm_num))
        _ =
          D.influencePrefactor *
            D.ratio ^ D.distance target source := by
              unfold influencePrefactor
              ring

noncomputable def remoteRowMass
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    D.remoteInfluenceProfile target source

theorem remoteRowMass_le
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    D.remoteRowMass target ≤
      D.influencePrefactor / (1 - 18 * D.ratio) := by
  unfold remoteRowMass
  exact
    periodicHypercubicEvenSpatialSlice_remoteMass_le_of_exponential_distance_decay
      H target
      (D.distance target)
      D.radius D.ratio D.influencePrefactor
      D.ratio_nonneg D.growth_mul_ratio_lt_one
      D.influencePrefactor_nonneg
      (D.distance_lt_radius target)
      (D.reachable target)
      (D.remoteInfluenceProfile target)
      (D.remoteInfluenceProfile_le target)

noncomputable def localInfluenceProfile
    {H : ℕ}
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source ∈
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target then
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
      beta
  else 0

theorem localInfluenceProfile_sum_le
    {H : ℕ}
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      localInfluenceProfile beta target source) ≤
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
  have hCard :
      (neighbors.card : ℝ) ≤ 18 := by
    exact_mod_cast
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors_card_le_eighteen
        H target
  have hEq :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        localInfluenceProfile beta target source) =
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

theorem refinedInfluence_eq_local_add_remote
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source =
      localInfluenceProfile beta target source +
        D.remoteInfluenceProfile target source := by
  classical
  by_cases hdiag : source = target
  · subst source
    simp [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
      localInfluenceProfile,
      remoteInfluenceProfile,
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
        localInfluenceProfile,
        remoteInfluenceProfile,
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
        localInfluenceProfile,
        remoteInfluenceProfile,
        hdiag, hlocal, hnotmem]

noncomputable def coefficient
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R) : ℝ :=
  18 *
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
        beta +
    D.influencePrefactor / (1 - 18 * D.ratio)

theorem coefficient_nonneg
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R) :
    0 ≤ D.coefficient := by
  unfold coefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
        beta hbeta))
    (div_nonneg D.influencePrefactor_nonneg
      (sub_nonneg.mpr (le_of_lt D.growth_mul_ratio_lt_one)))

theorem refinedRowSum_le_coefficient
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source) ≤
      D.coefficient := by
  have hLocal :=
    localInfluenceProfile_sum_le beta hbeta target
  have hRemote := D.remoteRowMass_le target
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta R.epsilon target source) =
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        localInfluenceProfile beta target source) +
      D.remoteRowMass target := by
        unfold remoteRowMass
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro source _hSource
        exact D.refinedInfluence_eq_local_add_remote target source
    _ ≤
      18 *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
            beta +
        D.influencePrefactor / (1 - 18 * D.ratio) :=
      add_le_add hLocal hRemote
    _ = D.coefficient := rfl

noncomputable def toDobrushinData
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData
        R)
    (hStrict : D.coefficient < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
      H N hN beta hbeta B := by
  let I := R.toRefinedInfluenceData B
  refine
    { toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData := I
      coefficient := D.coefficient
      coefficient_nonneg := D.coefficient_nonneg
      rowSum_le_coefficient := ?_
      coefficient_lt_one := hStrict }
  intro target
  dsimp [I]
  exact D.refinedRowSum_le_coefficient target

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorSpatialRemoteResponseDecayData

end

end MathlibAnalytic
end MGAP4D
