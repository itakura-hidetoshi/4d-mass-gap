import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureNorm
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureMeasurability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter

noncomputable section

/-- A real Hilbert feature map is continuous whenever its scalar kernel is
jointly continuous.

The proof uses the exact identity

`‖φ(y) - φ(x)‖² = K(y,y) - 2 K(y,x) + K(x,x)`

and continuity of the square root on the nonnegative squared distance. -/
theorem RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
    {X : Type}
    [TopologicalSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (hkernel : Continuous fun p : X × X => kernel p.1 p.2) :
    Continuous C.feature := by
  rw [continuous_iff_continuousAt]
  intro x
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let r : X → ℝ := fun y =>
    kernel y y - 2 * kernel y x + kernel x x
  have hdiag : Continuous fun y : X => kernel y y :=
    hkernel.comp (continuous_id.prodMk continuous_id)
  have hcross : Continuous fun y : X => kernel y x :=
    hkernel.comp (continuous_id.prodMk continuous_const)
  have hr : Continuous r := by
    dsimp [r]
    exact (hdiag.sub (continuous_const.mul hcross)).add continuous_const
  have hnorm : ∀ y, ‖C.feature y - C.feature x‖ = Real.sqrt (r y) := by
    intro y
    rw [← Real.sqrt_sq (norm_nonneg (C.feature y - C.feature x))]
    congr 1
    rw [norm_sub_sq_real]
    rw [← real_inner_self_eq_norm_sq (C.feature y),
      ← real_inner_self_eq_norm_sq (C.feature x)]
    rw [← C.kernel_eq_inner y y, ← C.kernel_eq_inner y x,
      ← C.kernel_eq_inner x x]
    rfl
  have hq : ContinuousAt (fun y => ‖C.feature y - C.feature x‖) x := by
    rw [show (fun y => ‖C.feature y - C.feature x‖) =
        fun y => Real.sqrt (r y) by
      funext y
      exact hnorm y]
    exact (Real.continuous_sqrt.comp hr).continuousAt
  have hevent := (Metric.tendsto_nhds.1 hq) ε hε
  filter_upwards [hevent] with y hy
  simpa [dist_eq_norm] using hy

/-- The one-plaquette Wilson Boltzmann central function is continuous. -/
theorem continuous_specialUnitaryWilsonBoltzmannCentralFunction
    (N : ℕ)
    (beta : ℝ) :
    Continuous (specialUnitaryWilsonBoltzmannCentralFunction N beta) := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  exact Real.continuous_exp.comp
    (continuous_const.mul
      (continuous_specialUnitaryWilsonPlaquetteEnergy N))

/-- The exact relative Wilson kernel is jointly continuous on `SU(N) × SU(N)`. -/
theorem continuous_specialUnitaryWilsonRelativeKernel
    (N : ℕ)
    (beta : ℝ) :
    Continuous fun p :
      Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      specialUnitaryWilsonRelativeKernel N beta p.1 p.2 := by
  unfold specialUnitaryWilsonRelativeKernel
  exact (continuous_specialUnitaryWilsonBoltzmannCentralFunction N beta).comp
    (continuous_fst.inv.mul continuous_snd)

/-- The exact Moore--Aronszajn Wilson RKHS feature map is continuous. -/
theorem continuous_specialUnitaryWilsonRelativeKernelFeature_feature
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (specialUnitaryWilsonRelativeKernelFeature N hN beta hbeta).feature :=
  RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
    (specialUnitaryWilsonRelativeKernelFeature N hN beta hbeta)
    (continuous_specialUnitaryWilsonRelativeKernel N beta)

/-- An almost-everywhere strongly measurable positive-half holonomy produces an
almost-everywhere strongly measurable exact local Wilson RKHS feature. -/
theorem localCrossingWilsonKernelConcreteFeature_feature_aestronglyMeasurable
    {X : Type}
    [MeasurableSpace X]
    {μ : Measure X}
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (positiveHalfHolonomy :
      X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hHolonomy : AEStronglyMeasurable positiveHalfHolonomy μ) :
    AEStronglyMeasurable
      (localCrossingWilsonKernelConcreteFeature
        N hN beta hbeta positiveHalfHolonomy).feature
      μ := by
  have hFeature :=
    (continuous_specialUnitaryWilsonRelativeKernelFeature_feature
      N hN beta hbeta).comp_aestronglyMeasurable hHolonomy
  simpa [localCrossingWilsonKernelConcreteFeature,
    localCrossingWilsonKernelFeature,
    RealHilbertKernelFeature.comap,
    localCrossingWilsonKernel] using hFeature

end

end MathlibAnalytic
end MGAP4D
