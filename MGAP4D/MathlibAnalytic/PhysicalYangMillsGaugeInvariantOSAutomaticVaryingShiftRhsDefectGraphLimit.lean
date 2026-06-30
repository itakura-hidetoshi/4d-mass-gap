import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVaryingShiftRhsDefectGraphLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Convergence of the shifts below the continuum coercive threshold already
forces the boundedness needed for full graph convergence; no separate bound on
the approximate vectors is required. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_graph_tendsto_continuumResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambdaSeq : ℕ → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {ySeq : ℕ → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaSeq atTop (nhds lambda))
    (hy : Tendsto ySeq atTop (nhds y))
    (hResidual : Tendsto
      (fun n => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) - lambdaSeq n • u n - ySeq n)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (u n,
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1 (u n)))
      atTop
      (nhds
        (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y,
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))) := by
  let r : ℕ → P.VacuumOrthogonalHilbert := fun n =>
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) -
        lambdaSeq n • u n - ySeq n
  have hr : Tendsto r atTop (nhds 0) := by
    simpa [r] using hResidual
  let source : ℕ → P.VacuumOrthogonalHilbert := fun n => ySeq n + r n
  have hSource : Tendsto source atTop (nhds y) := by
    simpa [source] using hy.add hr
  obtain ⟨Csource, hCsource⟩ :=
    (Metric.isBounded_range_of_tendsto source hSource).subset_closedBall
      (0 : P.VacuumOrthogonalHilbert)
  have hSourceNorm (n : ℕ) : ‖source n‖ ≤ Csource := by
    have hmem := hCsource (show source n ∈ Set.range source from ⟨n, rfl⟩)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
  let mu : ℝ := (lambda + G.mass / 2) / 2
  have hLambdaMu : lambda < mu := by
    dsimp [mu]
    linarith
  have hMuGap : mu < G.mass / 2 := by
    dsimp [mu]
    linarith
  have hLambdaEventually : ∀ᶠ n in atTop, lambdaSeq n < mu :=
    hLambda.eventually (Iio_mem_nhds hLambdaMu)
  let C : ℝ := (G.mass / 2 - mu)⁻¹ * Csource
  have hEventuallyBound : ∀ᶠ n in atTop, ‖u n‖ ≤ C := by
    filter_upwards [hLambdaEventually] with n hLambdaN
    have hLambdaNGap : lambdaSeq n < G.mass / 2 :=
      lt_trans hLambdaN hMuGap
    have hSourceEq :
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambdaSeq n • u n = source n := by
      dsimp [source, r]
      abel
    have hInverse :=
      G.admissibleRescaledDefectResolvent_apply_shift
        T hInnerSymmetric (tau n) hLambdaNGap (u n)
    rw [hSourceEq] at hInverse
    have hResolventBound :
        ‖G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau n) hLambdaNGap (source n)‖ ≤
          (G.mass / 2 - lambdaSeq n)⁻¹ * ‖source n‖ :=
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
        (G.admissibleRescaledDefectData hInnerSymmetric (tau n))
        hLambdaNGap
        (source n)
    have hDenN : 0 < G.mass / 2 - lambdaSeq n := sub_pos.mpr hLambdaNGap
    have hDenMu : 0 < G.mass / 2 - mu := sub_pos.mpr hMuGap
    have hInvLe :
        (G.mass / 2 - lambdaSeq n)⁻¹ ≤ (G.mass / 2 - mu)⁻¹ :=
      (inv_le_inv₀ hDenN hDenMu).2 (by linarith)
    calc
      ‖u n‖ =
          ‖G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau n) hLambdaNGap (source n)‖ := by
        rw [hInverse]
      _ ≤ (G.mass / 2 - lambdaSeq n)⁻¹ * ‖source n‖ := hResolventBound
      _ ≤ (G.mass / 2 - mu)⁻¹ * ‖source n‖ :=
        mul_le_mul_of_nonneg_right hInvLe (norm_nonneg _)
      _ ≤ (G.mass / 2 - mu)⁻¹ * Csource :=
        mul_le_mul_of_nonneg_left (hSourceNorm n) (inv_nonneg.mpr hDenMu.le)
      _ = C := by rfl
  have hLambdaError :
      Tendsto (fun n => lambdaSeq n - lambda) atTop (nhds 0) := by
    simpa using hLambda.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => lambda) atTop (nhds lambda))
  have hShiftNormLe :
      ∀ᶠ n in atTop,
        ‖lambdaSeq n • u n - lambda • u n‖ ≤
          ‖lambdaSeq n - lambda‖ * C := by
    filter_upwards [hEventuallyBound] with n hBoundN
    rw [← sub_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left hBoundN (norm_nonneg _)
  have hShiftMajorant :
      Tendsto (fun n => ‖lambdaSeq n - lambda‖ * C) atTop (nhds 0) := by
    have hConstC : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
    simpa using hLambdaError.norm.mul hConstC
  have hShiftError :
      Tendsto
        (fun n => lambdaSeq n • u n - lambda • u n)
        atTop
        (nhds 0) :=
    squeeze_zero_norm' hShiftNormLe hShiftMajorant
  have hResidualFixedRaw :
      Tendsto
        (fun n =>
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambdaSeq n • u n - ySeq n) +
            (lambdaSeq n • u n - lambda • u n))
        atTop
        (nhds 0) := by
    simpa using hResidual.add hShiftError
  have hResidualFunction :
      (fun n =>
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambdaSeq n • u n - ySeq n) +
          (lambdaSeq n • u n - lambda • u n)) =
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - ySeq n) := by
    funext n
    abel
  rw [hResidualFunction] at hResidualFixedRaw
  exact
    G.approximateShiftedAdmissibleRescaledDefect_varyingRhs_graph_tendsto_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf hlambda hTau hy hResidualFixedRaw

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
