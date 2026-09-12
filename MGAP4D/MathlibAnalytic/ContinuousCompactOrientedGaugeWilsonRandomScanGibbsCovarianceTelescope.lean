import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanCenteredIteration
import Mathlib.Tactic

/-!
# Finite random-scan Gibbs covariance telescope

The actual bounded-continuous random-scan observable is now iterated together
with an exact centered variation profile.  This file performs the finite
covariance telescope before any limiting argument.

For `R` the exact uniform random-scan heat-bath operator and `O_m = R^m O`,

`Cov(F,O) = sum_{m<M} Cov(F,(I-R)O_m) + Cov(F,O_M)`.

The two-sided local Dirichlet estimate then gives a finite partial-telescope
bound whose accumulated variation is exactly the already constructed finite
random-scan resolvent profile:

`|Cov(F,O) - Cov(F,O_M)| <= sum_e delta_e(F) w_M(e)`.

Everything here is finite-volume and finite in the random-scan update count.
No remainder limit, spatial clustering conclusion, continuum limit, or
Hamiltonian mass-gap statement is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One covariance step splits exactly into the random-scan Dirichlet defect
and the covariance of the next actual Feller random-scan observable. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_step
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : BoundedContinuousFunction C.base.Configuration ℝ)
    (S : ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => S.observable A) =
      C.gibbsCovarianceReal (fun A => F A)
          (fun A => C.randomScanHeatBathFluctuationContinuousBCF S.observable A) +
        C.gibbsCovarianceReal (fun A => F A)
          (fun A => (S.randomScanStep D).observable A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathFluctuationContinuousBCF
    ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState.randomScanStep
  rw [continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf]
  ring

/-- Exact finite covariance telescope along the actual bounded-continuous
random-scan orbit. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_telescope
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : BoundedContinuousFunction C.base.Configuration ℝ)
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (M : ℕ) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => O A) =
      (Finset.range M).sum
          (fun m =>
            C.gibbsCovarianceReal (fun A => F A)
              (fun A =>
                C.randomScanHeatBathFluctuationContinuousBCF
                  ((P.toRandomScanCenteredState).randomScanIterate D m).observable A)) +
        C.gibbsCovarianceReal (fun A => F A)
          (fun A =>
            ((P.toRandomScanCenteredState).randomScanIterate D M).observable A) := by
  induction M with
  | zero =>
      simp [ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState.randomScanIterate,
        ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.toRandomScanCenteredState]
  | succ M ih =>
      rw [Finset.sum_range_succ]
      calc
        C.gibbsCovarianceReal (fun A => F A) (fun A => O A) =
            (Finset.range M).sum
                (fun m =>
                  C.gibbsCovarianceReal (fun A => F A)
                    (fun A =>
                      C.randomScanHeatBathFluctuationContinuousBCF
                        ((P.toRandomScanCenteredState).randomScanIterate D m).observable A)) +
              C.gibbsCovarianceReal (fun A => F A)
                (fun A =>
                  ((P.toRandomScanCenteredState).randomScanIterate D M).observable A) := ih
        _ =
            (Finset.range M).sum
                (fun m =>
                  C.gibbsCovarianceReal (fun A => F A)
                    (fun A =>
                      C.randomScanHeatBathFluctuationContinuousBCF
                        ((P.toRandomScanCenteredState).randomScanIterate D m).observable A)) +
              (C.gibbsCovarianceReal (fun A => F A)
                  (fun A =>
                    C.randomScanHeatBathFluctuationContinuousBCF
                      ((P.toRandomScanCenteredState).randomScanIterate D M).observable A) +
                C.gibbsCovarianceReal (fun A => F A)
                  (fun A =>
                    (((P.toRandomScanCenteredState).randomScanIterate D M).randomScanStep D).observable A)) := by
              rw [continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_step]
        _ =
            ((Finset.range M).sum
                (fun m =>
                  C.gibbsCovarianceReal (fun A => F A)
                    (fun A =>
                      C.randomScanHeatBathFluctuationContinuousBCF
                        ((P.toRandomScanCenteredState).randomScanIterate D m).observable A)) +
              C.gibbsCovarianceReal (fun A => F A)
                (fun A =>
                  C.randomScanHeatBathFluctuationContinuousBCF
                    ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)) +
              C.gibbsCovarianceReal (fun A => F A)
                (fun A =>
                  ((P.toRandomScanCenteredState).randomScanIterate D (M + 1)).observable A) := by
            rw [continuous_compact_oriented_randomScanCenteredState_iterate_succ]
            ring

/-- Finite algebra: averaging the dot products against all variation iterates is
exactly the dot product against the normalized finite resolvent profile. -/
theorem continuous_compact_oriented_randomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (a variation : C.base.geometry.Edge → ℝ)
    (M : ℕ) :
    (Finset.range M).sum
        (fun m =>
          (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
            ∑ e : C.base.geometry.Edge,
              a e *
                continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                  D variation m e) =
      ∑ e : C.base.geometry.Edge,
        a e *
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
            D variation M e := by
  classical
  let n : ℝ := Fintype.card C.base.geometry.Edge
  calc
    (Finset.range M).sum
        (fun m =>
          n⁻¹ *
            ∑ e : C.base.geometry.Edge,
              a e *
                continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                  D variation m e) =
      n⁻¹ *
        (Finset.range M).sum
          (fun m =>
            ∑ e : C.base.geometry.Edge,
              a e *
                continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                  D variation m e) := by
        rw [← Finset.mul_sum]
    _ = n⁻¹ *
        ∑ e : C.base.geometry.Edge,
          (Finset.range M).sum
            (fun m =>
              a e *
                continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                  D variation m e) := by
        rw [Finset.sum_comm]
    _ = n⁻¹ *
        ∑ e : C.base.geometry.Edge,
          a e *
            (Finset.range M).sum
              (fun m =>
                continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                  D variation m e) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.mul_sum]
    _ = ∑ e : C.base.geometry.Edge,
        a e *
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
            D variation M e := by
      unfold continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [continuous_compact_oriented_dobrushinRandomScanVariationPartialSum_eq_sum]
      ring

/-- The finite covariance telescope is controlled by the source variation of
`F` paired with the normalized finite random-scan resolvent profile generated by
`O`.  This is the exact finite bridge from the local Dirichlet comparison to
the geometric resolvent estimates. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_partial_telescope_abs_le_finiteResolventProfile
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (F : BoundedContinuousFunction C.base.Configuration ℝ)
    (PF : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => F A))
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (M : ℕ) :
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A) -
        C.gibbsCovarianceReal (fun A => F A)
          (fun A =>
            ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)| ≤
      ∑ e : C.base.geometry.Edge,
        PF.variation e *
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
            D P.variation M e := by
  classical
  let S : ℕ → ContinuousCompactOrientedGaugeWilsonRandomScanCenteredState C :=
    fun m => (P.toRandomScanCenteredState).randomScanIterate D m
  have hTel :=
    continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_telescope
      C F P D M
  have hDiff :
      C.gibbsCovarianceReal (fun A => F A) (fun A => O A) -
          C.gibbsCovarianceReal (fun A => F A) (fun A => (S M).observable A) =
        (Finset.range M).sum
          (fun m =>
            C.gibbsCovarianceReal (fun A => F A)
              (fun A =>
                C.randomScanHeatBathFluctuationContinuousBCF (S m).observable A)) := by
    simpa [S] using
      congrArg
        (fun x => x -
          C.gibbsCovarianceReal (fun A => F A) (fun A => (S M).observable A))
        hTel
  rw [hDiff]
  calc
    |(Finset.range M).sum
        (fun m =>
          C.gibbsCovarianceReal (fun A => F A)
            (fun A =>
              C.randomScanHeatBathFluctuationContinuousBCF (S m).observable A))| ≤
      (Finset.range M).sum
        (fun m =>
          |C.gibbsCovarianceReal (fun A => F A)
            (fun A =>
              C.randomScanHeatBathFluctuationContinuousBCF (S m).observable A)|) := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range M).sum
        (fun m =>
          (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
            ∑ e : C.base.geometry.Edge,
              PF.variation e *
                continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                  D P.variation m e) := by
      apply Finset.sum_le_sum
      intro m _
      have hLocal :=
        continuous_compact_oriented_gibbsCovarianceReal_randomScanHeatBathFluctuation_abs_le_average_variation_products
          C hEdge F (S m).observable PF
            (S m).profile.toContinuousCompactOrientedGaugeWilsonLinkVariationBound
      simpa [S,
        continuous_compact_oriented_randomScanCenteredState_iterate_variation_eq P D m] using
        hLocal
    _ = ∑ e : C.base.geometry.Edge,
        PF.variation e *
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
            D P.variation M e := by
      exact
        continuous_compact_oriented_randomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile
          D PF.variation P.variation M

end

end MathlibAnalytic
end MGAP4D
