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
  let A := P.VacuumOrthogonalHilbert →L[ℝ]
    P.VacuumOrthogonalHilbert
  letI : IsBoundedSMul ℝ A :=
    IsBoundedSMul.of_norm_smul_le fun r R =>
      ContinuousLinearMap.opNorm_smul_le r R
  let Rlambda := G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
  let perturb : ℝ → A :=
    fun mu => (mu - lambda) • Rlambda
  let candidate : ℝ → A :=
    fun mu => Ring.inverse (1 - perturb mu) * Rlambda
  have hscalar : AnalyticAt ℝ (fun mu : ℝ => mu - lambda) lambda := by
    fun_prop
  have hconstR : AnalyticAt ℝ (fun _ : ℝ => Rlambda) lambda :=
    analyticAt_const
  have hperturb : AnalyticAt ℝ perturb lambda := by
    with_reducible_and_instances
      simpa only [perturb, Pi.smul_apply] using hscalar.smul hconstR
  have hperturbZero : perturb lambda = 0 := by
    dsimp [perturb]
    rw [sub_self]
    exact zero_smul ℝ Rlambda
  have hinverse :
      AnalyticAt ℝ (fun mu => Ring.inverse (1 - perturb mu)) lambda := by
    have houter := analyticAt_inverse_one_sub ℝ A
    have hcomp := houter.comp_of_eq hperturb hperturbZero
    simpa only [Function.comp_apply] using hcomp
  have hcandidate : AnalyticAt ℝ candidate lambda := by
    dsimp [candidate]
    with_reducible_and_instances
      exact hinverse.mul analyticAt_const
  have hperturbTendsto : Tendsto perturb (𝓝 lambda) (𝓝 0) := by
    have hcont := hperturb.continuousAt
    change Tendsto perturb (𝓝 lambda) (𝓝 (perturb lambda)) at hcont
    rw [hperturbZero] at hcont
    exact hcont
  have hsmall : ∀ᶠ mu in 𝓝 lambda, ‖perturb mu‖ < 1 := by
    have hopen : IsOpen {R : A | ‖R‖ < 1} := by
      with_reducible_and_instances
        exact isOpen_lt continuous_norm continuous_const
    have hzero : (0 : A) ∈ {R : A | ‖R‖ < 1} := by
      simp
    exact hperturbTendsto.eventually (hopen.mem_nhds hzero)
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
    have hneg :
        (lambda - mu) • (Rlambda.comp Rmu) =
          -((mu - lambda) • (Rlambda.comp Rmu)) := by
      calc
        (lambda - mu) • (Rlambda.comp Rmu) =
            (-(mu - lambda)) • (Rlambda.comp Rmu) := by
          congr 1
          ring
        _ = -((mu - lambda) • (Rlambda.comp Rmu)) := by
          exact neg_smul (mu - lambda) (Rlambda.comp Rmu)
    have hid' :
        Rmu - (mu - lambda) • (Rlambda.comp Rmu) = Rlambda := by
      rw [sub_eq_add_neg, ← hneg, ← hid]
      abel
    have hmul : (1 - perturb mu) * Rmu = Rlambda := by
      dsimp [perturb]
      rw [sub_mul, one_mul]
      simpa [ContinuousLinearMap.mul_def] using hid'
    rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hmu]
    dsimp [candidate]
    rw [NormedRing.inverse_one_sub (perturb mu) hmuSmall]
    let u := Units.oneSub (perturb mu) hmuSmall
    calc
      (↑u⁻¹ : A) * Rlambda =
          (↑u⁻¹ : A) * ((1 - perturb mu) * Rmu) := by
        rw [hmul]
      _ = (↑u⁻¹ : A) * ((↑u : A) * Rmu) := by
        simp [u]
      _ = Rmu := by
        rw [← mul_assoc]
        simp
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
