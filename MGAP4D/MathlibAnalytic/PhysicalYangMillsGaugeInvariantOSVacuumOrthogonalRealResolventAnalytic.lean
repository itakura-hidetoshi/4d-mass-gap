import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventIteratedDerivativeNorm
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

set_option maxHeartbeats 1200000

/-- The vacuum-orthogonal real resolvent is real analytic at every parameter
strictly below the transferred mass.  Locally it is the geometric inverse of
`1 - (mu - lambda) R_lambda`, multiplied by `R_lambda`. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_analyticAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    AnalyticAt ℝ
      (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda := by
  let Rlambda := G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
  let perturb : ℝ →
      (P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert) :=
    fun mu => (mu - lambda) • Rlambda
  let candidate : ℝ →
      (P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert) :=
    fun mu => Ring.inverse (1 - perturb mu) * Rlambda
  have hperturb : AnalyticAt ℝ perturb lambda := by
    dsimp [perturb]
    fun_prop
  have hinverse :
      AnalyticAt ℝ (fun mu => Ring.inverse (1 - perturb mu)) lambda := by
    simpa [perturb] using
      (analyticAt_inverse_one_sub ℝ
        (P.VacuumOrthogonalHilbert →L[ℝ]
          P.VacuumOrthogonalHilbert)).comp hperturb
  have hcandidate : AnalyticAt ℝ candidate lambda := by
    dsimp [candidate]
    exact hinverse.mul analyticAt_const
  have hperturbTendsto : Tendsto perturb (𝓝 lambda) (𝓝 0) := by
    simpa [perturb] using hperturb.continuousAt
  have hsmall : ∀ᶠ mu in 𝓝 lambda, ‖perturb mu‖ < 1 := by
    have hball :
        Metric.ball
            (0 : P.VacuumOrthogonalHilbert →L[ℝ]
              P.VacuumOrthogonalHilbert) 1 ∈
          𝓝 (0 : P.VacuumOrthogonalHilbert →L[ℝ]
            P.VacuumOrthogonalHilbert) :=
      Metric.ball_mem_nhds _ one_pos
    filter_upwards [hperturbTendsto.eventually hball] with mu hmu
    simpa [Metric.mem_ball, dist_zero_right] using hmu
  have heq :
      candidate =ᶠ[𝓝 lambda]
        G.vacuumOrthogonalRealResolventOn T hP hSelf := by
    filter_upwards [hsmall, Iio_mem_nhds hlambda] with mu hmuSmall hmu
    let Rmu := G.vacuumOrthogonalRealResolvent T hP hSelf hmu
    have hid :
        Rlambda - Rmu =
          (lambda - mu) • (Rlambda.comp Rmu) := by
      simpa [Rlambda, Rmu] using
        G.vacuumOrthogonalRealResolvent_identity
          T hP hSelf hlambda hmu
    have hid' :
        Rmu - (mu - lambda) • (Rlambda.comp Rmu) = Rlambda := by
      module at hid ⊢
    have hmul : (1 - perturb mu) * Rmu = Rlambda := by
      dsimp [perturb]
      rw [sub_mul, one_mul, Algebra.smul_mul_assoc]
      simpa [ContinuousLinearMap.mul_def] using hid'
    rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hmu]
    dsimp [candidate]
    rw [NormedRing.inverse_one_sub (perturb mu) hmuSmall]
    rw [← hmul]
    change
      (↑(Units.oneSub (perturb mu) hmuSmall)⁻¹ :
          P.VacuumOrthogonalHilbert →L[ℝ]
            P.VacuumOrthogonalHilbert) *
        ((↑(Units.oneSub (perturb mu) hmuSmall) :
            P.VacuumOrthogonalHilbert →L[ℝ]
              P.VacuumOrthogonalHilbert) * Rmu) = Rmu
    simp [mul_assoc]
  exact hcandidate.congr heq

/-- Real analyticity of the total resolvent representative on the full open
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_analyticOnNhd
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    AnalyticOnNhd ℝ
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  intro lambda hlambda
  exact G.vacuumOrthogonalRealResolventOn_analyticAt
    T hP hSelf hlambda

/-- Within-set real analyticity on the open sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_analyticOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    AnalyticOn ℝ
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) :=
  (G.vacuumOrthogonalRealResolventOn_analyticOnNhd T hP hSelf).analyticOn

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
