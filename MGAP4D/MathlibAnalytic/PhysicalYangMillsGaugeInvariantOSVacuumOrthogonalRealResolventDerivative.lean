import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventParameterContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

set_option maxHeartbeats 800000

/-- A total real-parameter representative of the vacuum-orthogonal excitation
resolvent.  Outside the open sub-mass interval it is set to zero; all analytic
statements below are restricted to the interval where this auxiliary choice is
irrelevant. -/
noncomputable def FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (lambda : ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  if hlambda : lambda < G.mass then
    G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
  else
    0

@[simp] theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_of_lt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    G.vacuumOrthogonalRealResolventOn T hP hSelf lambda =
      G.vacuumOrthogonalRealResolvent T hP hSelf hlambda := by
  simp [vacuumOrthogonalRealResolventOn, hlambda]

/-- The total representative restricts to the previously constructed continuous
excitation-resolvent family on the open sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_continuousOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContinuousOn
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq :
      (Set.Iio G.mass).restrict
          (G.vacuumOrthogonalRealResolventOn T hP hSelf) =
        G.vacuumOrthogonalRealResolventFamily T hP hSelf := by
    funext lambda
    exact G.vacuumOrthogonalRealResolventOn_of_lt
      T hP hSelf lambda.property
  rw [heq]
  exact G.vacuumOrthogonalRealResolventFamily_continuous T hP hSelf

/-- The operator-norm derivative of the excitation resolvent within the real
sub-mass interval is the square of the resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_hasDerivWithinAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    HasDerivWithinAt
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      ((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda))
      (Set.Iio G.mass) lambda := by
  refine (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ)
    (f := G.vacuumOrthogonalRealResolventOn T hP hSelf)
    (f' := (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda))
    (s := Set.Iio G.mass)
    (x := lambda)).2 ?_
  let Rlambda := G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
  have hres0 :
      Tendsto
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (𝓝[Set.Iio G.mass] lambda)
        (𝓝 (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda)) :=
    G.vacuumOrthogonalRealResolventOn_continuousOn
      T hP hSelf lambda hlambda
  have hres :
      Tendsto
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (𝓝[Set.Iio G.mass] lambda) (𝓝 Rlambda) := by
    rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda] at hres0
    exact hres0
  have hres' :
      Tendsto
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (𝓝[Set.Iio G.mass \ {lambda}] lambda) (𝓝 Rlambda) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro mu hmu
      exact hmu.1
  have hcomp :
      Tendsto
        (fun mu =>
          (G.vacuumOrthogonalRealResolventOn T hP hSelf mu).comp Rlambda)
        (𝓝[Set.Iio G.mass \ {lambda}] lambda)
        (𝓝 (Rlambda.comp Rlambda)) := by
    exact
      (continuous_id.clm_comp_const Rlambda).continuousAt.tendsto.comp hres'
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with mu hmu
  rcases hmu with ⟨hmuMass, hmuNe⟩
  have hne : mu - lambda ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hmuNe
  rw [slope_def_module,
    G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hmuMass,
    G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda,
    G.vacuumOrthogonalRealResolvent_identity
      T hP hSelf hmuMass hlambda,
    inv_smul_smul₀ hne]

/-- Since the sub-mass interval is open, the within-derivative is the ordinary
operator-norm derivative at every sub-mass parameter. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_hasDerivAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    HasDerivAt
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      ((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda))
      lambda := by
  let d :=
    (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda)
  have hwithin :
      HasDerivWithinAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        d (Set.Iio G.mass) lambda := by
    simpa [d] using
      G.vacuumOrthogonalRealResolventOn_hasDerivWithinAt
        T hP hSelf hlambda
  have hfwithin :
      HasFDerivWithinAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (toSpanSingleton ℝ d) (Set.Iio G.mass) lambda :=
    hwithin.hasFDerivWithinAt
  have hfat :
      HasFDerivAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (toSpanSingleton ℝ d) lambda :=
    hfwithin.hasFDerivAt (Iio_mem_nhds hlambda)
  have hd :
      HasDerivAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        ((toSpanSingleton ℝ d) 1) lambda :=
    (hasFDerivAt_iff_hasDerivAt).1 hfat
  simpa [d] using hd

/-- Explicit operator-norm derivative formula for the excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_deriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) := by
  let d :=
    (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda)
  have hd :
      HasDerivAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        d lambda := by
    simpa [d] using
      G.vacuumOrthogonalRealResolventOn_hasDerivAt T hP hSelf hlambda
  have hf :
      HasFDerivAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (toSpanSingleton ℝ d) lambda :=
    hd.hasFDerivAt
  have hfd :
      fderiv ℝ (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
        toSpanSingleton ℝ d :=
    hf.fderiv
  unfold deriv
  rw [hfd]
  simp [d]

/-- The excitation resolvent is differentiable throughout the full real
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_differentiableOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    DifferentiableOn ℝ
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  intro lambda hlambda
  let d :=
    (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda)
  have hwithin :
      HasDerivWithinAt
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        d (Set.Iio G.mass) lambda := by
    simpa [d] using
      G.vacuumOrthogonalRealResolventOn_hasDerivWithinAt
        T hP hSelf hlambda
  exact ⟨toSpanSingleton ℝ d, hwithin.hasFDerivWithinAt⟩

/-- The derivative of the excitation resolvent is continuous on the open real
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_continuousOn_deriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContinuousOn
      (deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf))
      (Set.Iio G.mass) := by
  have hdiff :=
    G.vacuumOrthogonalRealResolventOn_differentiableOn T hP hSelf
  have hsquare :
      ContinuousOn
        (fun lambda =>
          (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda).comp
            (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda))
        (Set.Iio G.mass) :=
    (hdiff.clm_comp hdiff).continuousOn
  apply hsquare.congr
  intro lambda hlambda
  calc
    deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
          (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) :=
      G.vacuumOrthogonalRealResolventOn_deriv T hP hSelf hlambda
    _ = (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda).comp
          (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) := by
      rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda]

/-- The excitation resolvent is `C¹` in operator norm on the complete open real
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_contDiffOn_one
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ 1
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨G.vacuumOrthogonalRealResolventOn_differentiableOn
      T hP hSelf, ?_, ?_⟩
  · simp
  · simpa only [contDiffOn_zero] using
      G.vacuumOrthogonalRealResolventOn_continuousOn_deriv T hP hSelf

/-- Differentiability and `C¹` package for the excitation resolvent below the
transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventDerivative_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ 1
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) ∧
      DifferentiableOn ℝ
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < G.mass),
        deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
          (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
            (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) :=
  ⟨G.vacuumOrthogonalRealResolventOn_contDiffOn_one T hP hSelf,
    G.vacuumOrthogonalRealResolventOn_differentiableOn T hP hSelf,
    fun hlambda =>
      G.vacuumOrthogonalRealResolventOn_deriv T hP hSelf hlambda⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
