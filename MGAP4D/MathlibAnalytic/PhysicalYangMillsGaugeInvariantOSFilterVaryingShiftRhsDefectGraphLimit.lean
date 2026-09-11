import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAutomaticVaryingShiftRhsDefectGraphLimit
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

/-- The varying-time, varying-shift, varying-source graph convergence theorem
holds for an arbitrary indexing filter.  Only eventual boundedness is used. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι)
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {u : ι → P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hy : Tendsto yNet l (nhds y))
    (hResidual : Tendsto
      (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i)
      l (nhds 0)) :
    Tendsto
      (fun i => (u i, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 (u i)))
      l
      (nhds (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))) := by
  let r : ι → P.VacuumOrthogonalHilbert := fun i =>
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i) -
        lambdaNet i • u i - yNet i
  have hr : Tendsto r l (nhds 0) := by
    simpa [r] using hResidual
  let source : ι → P.VacuumOrthogonalHilbert := fun i => yNet i + r i
  have hSource : Tendsto source l (nhds y) := by
    simpa [source] using hy.add hr
  have hSourceEventually : ∀ᶠ i in l, ‖source i‖ ≤ ‖y‖ + 1 := by
    filter_upwards [hSource (Metric.ball_mem_nhds y zero_lt_one)] with i hi
    have hdist : dist (source i) y < 1 := by
      simpa [Metric.mem_ball] using hi
    calc
      ‖source i‖ = ‖(source i - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖source i - y‖ + ‖y‖ := norm_add_le _ _
      _ = dist (source i) y + ‖y‖ := by rw [dist_eq_norm]
      _ ≤ ‖y‖ + 1 := by linarith
  let mu : ℝ := (lambda + G.mass / 2) / 2
  have hLambdaMu : lambda < mu := by
    dsimp [mu]
    linarith
  have hMuGap : mu < G.mass / 2 := by
    dsimp [mu]
    linarith
  have hLambdaEventually : ∀ᶠ i in l, lambdaNet i < mu :=
    hLambda.eventually (Iio_mem_nhds hLambdaMu)
  let C : ℝ := (G.mass / 2 - mu)⁻¹ * (‖y‖ + 1)
  have hEventuallyBound : ∀ᶠ i in l, ‖u i‖ ≤ C := by
    filter_upwards [hLambdaEventually, hSourceEventually] with i hLambdaI hSourceI
    have hLambdaIGap : lambdaNet i < G.mass / 2 := lt_trans hLambdaI hMuGap
    have hSourceEq :
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) -
            lambdaNet i • u i = source i := by
      dsimp [source, r]
      abel
    have hInverse :=
      G.admissibleRescaledDefectResolvent_apply_shift
        T hInnerSymmetric (tau i) hLambdaIGap (u i)
    rw [hSourceEq] at hInverse
    have hResolventBound :
        ‖G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaIGap (source i)‖ ≤
          (G.mass / 2 - lambdaNet i)⁻¹ * ‖source i‖ :=
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
        (G.admissibleRescaledDefectData hInnerSymmetric (tau i))
        hLambdaIGap
        (source i)
    have hDenI : 0 < G.mass / 2 - lambdaNet i := sub_pos.mpr hLambdaIGap
    have hDenMu : 0 < G.mass / 2 - mu := sub_pos.mpr hMuGap
    have hInvLe :
        (G.mass / 2 - lambdaNet i)⁻¹ ≤ (G.mass / 2 - mu)⁻¹ :=
      (inv_le_inv₀ hDenI hDenMu).2 (by linarith)
    calc
      ‖u i‖ =
          ‖G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaIGap (source i)‖ := by
        rw [hInverse]
      _ ≤ (G.mass / 2 - lambdaNet i)⁻¹ * ‖source i‖ := hResolventBound
      _ ≤ (G.mass / 2 - mu)⁻¹ * ‖source i‖ :=
        mul_le_mul_of_nonneg_right hInvLe (norm_nonneg _)
      _ ≤ (G.mass / 2 - mu)⁻¹ * (‖y‖ + 1) :=
        mul_le_mul_of_nonneg_left hSourceI (inv_nonneg.mpr hDenMu.le)
      _ = C := by rfl
  have hLambdaError :
      Tendsto (fun i => lambdaNet i - lambda) l (nhds 0) := by
    simpa using hLambda.sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => lambda) l (nhds lambda))
  have hShiftNormLe :
      ∀ᶠ i in l,
        ‖lambdaNet i • u i - lambda • u i‖ ≤
          ‖lambdaNet i - lambda‖ * C := by
    filter_upwards [hEventuallyBound] with i hBoundI
    rw [← sub_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left hBoundI (norm_nonneg _)
  have hShiftMajorant :
      Tendsto (fun i => ‖lambdaNet i - lambda‖ * C) l (nhds 0) := by
    have hConstC : Tendsto (fun _ : ι => C) l (nhds C) := tendsto_const_nhds
    simpa using hLambdaError.norm.mul hConstC
  have hShiftError :
      Tendsto (fun i => lambdaNet i • u i - lambda • u i) l (nhds 0) :=
    squeeze_zero_norm' hShiftNormLe hShiftMajorant
  have hYError : Tendsto (fun i => yNet i - y) l (nhds 0) := by
    simpa using hy.sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => y) l (nhds y))
  have hFixedResidualRaw :
      Tendsto
        (fun i =>
          ((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau i).1 (u i) -
              lambdaNet i • u i - yNet i) +
            (lambdaNet i • u i - lambda • u i)) +
          (yNet i - y))
        l
        (nhds 0) := by
    simpa using (hResidual.add hShiftError).add hYError
  have hFixedResidualFunction :
      (fun i =>
        ((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) -
            lambdaNet i • u i - yNet i) +
          (lambdaNet i • u i - lambda • u i)) +
        (yNet i - y)) =
      (fun i =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) -
            lambda • u i - y) := by
    funext i
    abel
  rw [hFixedResidualFunction] at hFixedResidualRaw
  let q : ι → P.VacuumOrthogonalHilbert := fun i =>
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i) -
        lambda • u i - y
  have hq : Tendsto q l (nhds 0) := by
    simpa [q] using hFixedResidualRaw
  have hErrorEq (i : ι) :
      u i - G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hlambda y =
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hlambda (q i) := by
    let R := G.admissibleRescaledDefectResolvent hInnerSymmetric (tau i) hlambda
    have hInverse :
        R (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) - lambda • u i) = u i :=
      G.admissibleRescaledDefectResolvent_apply_shift
        T hInnerSymmetric (tau i) hlambda (u i)
    calc
      u i - R y =
          R (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) - lambda • u i) - R y := by
        rw [hInverse]
      _ = R ((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) - lambda • u i) - y) :=
        (R.map_sub _ _).symm
      _ = R (q i) := by rfl
  have hErrorNormLe (i : ι) :
      ‖u i - G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hlambda y‖ ≤
        (G.mass / 2 - lambda)⁻¹ * ‖q i‖ := by
    rw [hErrorEq i]
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
        (G.admissibleRescaledDefectData hInnerSymmetric (tau i)) hlambda (q i)
  have hMajorant :
      Tendsto (fun i => (G.mass / 2 - lambda)⁻¹ * ‖q i‖) l (nhds 0) := by
    simpa using tendsto_const_nhds.mul hq.norm
  have hError :
      Tendsto
        (fun i => u i - G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hlambda y)
        l
        (nhds 0) :=
    squeeze_zero_norm' (Eventually.of_forall hErrorNormLe) hMajorant
  have hSelected :
      Tendsto
        (fun i => G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau i) hlambda y)
        l
        (nhds (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y)) :=
    (G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y).comp hTau
  have hu :
      Tendsto u l (nhds (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y)) := by
    simpa only [sub_add_cancel, zero_add] using hError.add hSelected
  have hRight :
      Tendsto (fun i => y + lambda • u i) l
        (nhds (y + lambda • G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.smul hu)
  have hDefectRaw :
      Tendsto (fun i => q i + (y + lambda • u i)) l
        (nhds (y + lambda • G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y)) := by
    simpa only [zero_add] using hq.add hRight
  have hDefectFunction :
      (fun i => q i + (y + lambda • u i)) =
      (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 (u i)) := by
    funext i
    dsimp [q]
    abel
  rw [hDefectFunction] at hDefectRaw
  have hDefect :
      Tendsto
        (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i))
        l
        (nhds (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))) := by
    simpa only [
      G.vacuumOrthogonalClosedRightHamiltonian_apply_continuumResolventDomainPoint_eq
        T hP hInnerSymmetric hSelf hlambda y] using hDefectRaw
  exact hu.prodMk_nhds hDefect

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
