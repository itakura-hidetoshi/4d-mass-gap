import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderMathlibContDiffInfinity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology ContDiff BigOperators Pointwise

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

local instance wilsonCylinderTaylorSeriesCorePhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

private theorem wilsonCylinderTaylorSeries_hasDerivWithinAt_of_quadraticRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (s : Set ℝ) (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (_hx : x ∈ s)
    (hrem : ∀ y ∈ s,
      ‖f y - f x - (y - x) • f' x‖ ≤ B * ‖y - x‖ ^ 2) :
    HasDerivWithinAt f (f' x) s x := by
  rw [hasDerivWithinAt_iff_tendsto]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro epsilon hepsilon
  let D := B + 1
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hBD : B ≤ D := by
    dsimp [D]
    linarith
  refine ⟨epsilon / D, div_pos hepsilon hD, ?_⟩
  intro y hy hdist
  by_cases hxy : y = x
  · subst y
    simp [hepsilon]
  · have hsub : y - x ≠ 0 := sub_ne_zero.mpr hxy
    have hnorm : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    have hr := hrem y hy
    have hqnonneg :
        0 ≤ ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
    have hdx : ‖y - x‖ < epsilon / D := by
      simpa [Real.dist_eq] using hdist
    have hq :
        ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ < epsilon := by
      calc
        ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ ≤
            ‖y - x‖⁻¹ * (B * ‖y - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg _))
        _ = B * ‖y - x‖ := by
          field_simp [hnorm]
        _ ≤ D * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hBD (norm_nonneg _)
        _ < D * (epsilon / D) :=
          mul_lt_mul_of_pos_left hdx hD
        _ = epsilon := by
          field_simp [ne_of_gt hD]
    simpa [Real.dist_eq, abs_of_nonneg hqnonneg] using hq

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_derivWithin_Icc
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    derivWithin
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Icc beta gamma) t =
      -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN (m + 1) t := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ (m + 2)
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := pow_nonneg hC (m + 2)
  have ht0 : 0 ≤ t := hbeta.trans ht.1
  have hraw :=
    wilsonCylinderTaylorSeries_hasDerivWithinAt_of_quadraticRemainder
      (f := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (f' := fun u =>
        -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + 1) u)
      (s := Set.Icc beta gamma) B hB t ht
      (by
        intro y hy
        have hy0 : 0 ≤ y := hbeta.trans hy.1
        simpa [B, C] using
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_quadraticRemainder
            H N hN m t y ht0 hy0)
  exact hraw.derivWithin ((uniqueDiffOn_Icc hbg) t ht)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_iteratedDerivWithin_Icc
    (H N : ℕ) (hN : 0 < N) (m n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Icc beta gamma) t =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + n) t := by
  induction n generalizing t with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hEqOn :
          Set.EqOn
            (iteratedDerivWithin n
              (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                H N hN m)
              (Set.Icc beta gamma))
            (fun u : ℝ =>
              ((-1 : ℝ) ^ n) •
                periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                  H N hN (m + n) u)
            (Set.Icc beta gamma) := by
        intro u hu
        exact ih u hu
      rw [derivWithin_congr hEqOn (ih t ht)]
      let F :=
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + n)
      let c : ℝ := (-1 : ℝ) ^ n
      let C :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
      let B := C ^ ((m + n) + 2)
      have hC : 0 ≤ C := by
        simpa [C] using
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
      have hB : 0 ≤ B := pow_nonneg hC ((m + n) + 2)
      have ht0 : 0 ≤ t := hbeta.trans ht.1
      have hbaseRaw :=
        wilsonCylinderTaylorSeries_hasDerivWithinAt_of_quadraticRemainder
          (f := F)
          (f' := fun u =>
            -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN (m + n + 1) u)
          (s := Set.Icc beta gamma) B hB t ht
          (by
            intro y hy
            have hy0 : 0 ≤ y := hbeta.trans hy.1
            simpa [F, B, C, Nat.add_assoc] using
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_quadraticRemainder
                H N hN (m + n) t y ht0 hy0)
      have hunique := (uniqueDiffOn_Icc hbg) t ht
      have hscaled0 := (hbaseRaw.const_smul c).derivWithin hunique
      have hscaled :
          derivWithin (fun u : ℝ => c • F u) (Set.Icc beta gamma) t =
            c • (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN (m + n + 1) t) := by
        simpa only [Pi.smul_apply] using hscaled0
      change derivWithin (fun u : ℝ => c • F u) (Set.Icc beta gamma) t = _
      rw [hscaled, smul_neg]
      dsimp [c]
      have hidx : m + n + 1 = m + (n + 1) := by omega
      rw [hidx]
      have hsign : (-1 : ℝ) ^ (n + 1) = - ((-1 : ℝ) ^ n) := by
        rw [pow_succ]
        ring
      rw [hsign]
      exact (neg_smul ((-1 : ℝ) ^ n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + (n + 1)) t)).symm

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Icc beta gamma) t =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_iteratedDerivWithin_Icc
    H N hN 0 n beta gamma t hbeta hbg ht]
  simp only [Nat.zero_add]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN n t (hbeta.trans ht.1)]

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc_norm_le
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    ‖iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Icc beta gamma) t‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ n := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
    H N hN n beta gamma t hbeta hbg ht]
  calc
    ‖((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1)‖ ≤
      ‖((-1 : ℝ) ^ n)‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1)‖ := by
      rw [norm_pow]
      simp
    _ ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ n :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
        H N hN n t (hbeta.trans ht.1)

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : ℝ) (k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  (((k.factorial : ℝ)⁻¹ * (gamma - beta) ^ k) •
    (((-1 : ℝ) ^ k) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN k beta hbeta))

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_taylorWithinEval_eq_WilsonTaylorSum
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma) :
    taylorWithinEval
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      n (Set.Icc beta gamma) beta gamma =
      ∑ k ∈ Finset.range (n + 1),
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
    H N hN k beta gamma beta hbeta hbg (left_mem_Icc.mpr hbg.le)]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
  rfl

end
end MathlibAnalytic
end MGAP4D