import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyConjugation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pull a Hilbert kernel feature realization back along an arbitrary map. -/
noncomputable def RealHilbertKernelFeature.comap
    {X Y : Type}
    {kernel : Y → Y → ℝ}
    (C : RealHilbertKernelFeature Y kernel)
    (f : X → Y) :
    RealHilbertKernelFeature X (fun x y => kernel (f x) (f y)) where
  FeatureHilbert := C.FeatureHilbert
  feature := fun x => C.feature (f x)
  kernel_eq_inner x y := C.kernel_eq_inner (f x) (f y)

/-- The one-plaquette Wilson Boltzmann central function on `SU(N)`. -/
def specialUnitaryWilsonBoltzmannCentralFunction
    (N : ℕ)
    (beta : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy N U)

/-- The Wilson Boltzmann factor is a central function. -/
theorem specialUnitaryWilsonBoltzmannCentralFunction_conjInvariant
    {N : ℕ}
    (beta : ℝ)
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonBoltzmannCentralFunction N beta (h * g * h⁻¹) =
      specialUnitaryWilsonBoltzmannCentralFunction N beta g := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  rw [specialUnitaryWilsonPlaquetteEnergy_conjInvariant]

/-- Split the Wilson Boltzmann factor into its constant part and normalized
real-trace part. -/
theorem specialUnitaryWilsonBoltzmannCentralFunction_eq_trace
    (N : ℕ)
    (beta : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonBoltzmannCentralFunction N beta U =
      Real.exp (-beta) *
        Real.exp (beta * normalizedSpecialUnitaryRealTrace N U) := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  rw [show -beta * (1 - normalizedSpecialUnitaryRealTrace N U) =
      -beta + beta * normalizedSpecialUnitaryRealTrace N U by ring]
  exact Real.exp_add _ _

/-- The normalized real-trace relative kernel underlying the Wilson
Boltzmann kernel. -/
def specialUnitaryNormalizedTraceRelativeKernel
    (N : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  normalizedSpecialUnitaryRealTrace N (g⁻¹ * h)

/-- The relative one-plaquette Wilson kernel on `SU(N)`. -/
def specialUnitaryWilsonRelativeKernel
    (N : ℕ)
    (beta : ℝ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  specialUnitaryWilsonBoltzmannCentralFunction N beta (g⁻¹ * h)

/-- For positive rank and nonnegative coupling, the exact one-plaquette Wilson
relative kernel lies between the explicit Boltzmann floor `exp (-2 * beta)` and
one.  This is the first pointwise quantitative bound on the concrete crossing
kernel used by the shared-boundary transfer construction. -/
theorem specialUnitaryWilsonRelativeKernel_mem_Icc
    {N : ℕ}
    (hN : 0 < N)
    {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta g h ∈
      Set.Icc (Real.exp (-2 * beta)) 1 := by
  have hE0 :
      0 ≤ specialUnitaryWilsonPlaquetteEnergy N (g⁻¹ * h) :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg hN (g⁻¹ * h)
  have hE2 :
      specialUnitaryWilsonPlaquetteEnergy N (g⁻¹ * h) ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two hN (g⁻¹ * h)
  unfold specialUnitaryWilsonRelativeKernel
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  constructor
  · apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hE2 hbeta
    linarith
  · rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta) hE0

/-- In particular, the exact one-plaquette Wilson relative kernel is strictly
positive at every pair of group elements. -/
theorem specialUnitaryWilsonRelativeKernel_pos
    {N : ℕ}
    (hN : 0 < N)
    {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 < specialUnitaryWilsonRelativeKernel N beta g h := by
  exact lt_of_lt_of_le
    (Real.exp_pos (-2 * beta))
    (specialUnitaryWilsonRelativeKernel_mem_Icc hN hbeta g h).1

/-- The relative Wilson kernel is the positive constant `exp (-beta)` times the
exponential of the normalized real-trace relative kernel. -/
theorem specialUnitaryWilsonRelativeKernel_eq_trace
    (N : ℕ)
    (beta : ℝ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta g h =
      Real.exp (-beta) *
        Real.exp
          (beta * specialUnitaryNormalizedTraceRelativeKernel N g h) := by
  unfold specialUnitaryWilsonRelativeKernel
  rw [specialUnitaryWilsonBoltzmannCentralFunction_eq_trace]
  rfl

/-- The relative Wilson kernel is invariant under simultaneous left
translation of its two arguments. -/
theorem specialUnitaryWilsonRelativeKernel_leftInvariant
    {N : ℕ}
    (beta : ℝ)
    (a g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta (a * g) (a * h) =
      specialUnitaryWilsonRelativeKernel N beta g h := by
  unfold specialUnitaryWilsonRelativeKernel
  rw [show (a * g)⁻¹ * (a * h) = g⁻¹ * h by group]

/-- Degree-`n` finite exponential approximation to the relative Wilson kernel.
The constant factor `exp (-beta)` is retained exactly. -/
def specialUnitaryWilsonRelativeKernelPartial
    (N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta) *
    RealHilbertKernelFeature.exponentialPartialKernel
      (specialUnitaryNormalizedTraceRelativeKernel N) beta n g h

/-- Once the normalized real-trace relative kernel has a Hilbert feature, every
finite Wilson exponential approximation has an explicit Hilbert feature. -/
noncomputable def specialUnitaryWilsonRelativeKernelPartialFeature
    (N : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryNormalizedTraceRelativeKernel N))
    (n : ℕ) :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernelPartial N beta n) := by
  simpa [specialUnitaryWilsonRelativeKernelPartial] using
    RealHilbertKernelFeature.nonnegSMul
      (Real.exp (-beta))
      (Real.exp_nonneg (-beta))
      (RealHilbertKernelFeature.exponentialPartial C beta hbeta n)

/-- The finite Wilson approximation is exactly the inner product of the
explicit finite completed-tensor-product feature. -/
theorem specialUnitaryWilsonRelativeKernelPartial_eq_inner
    (N : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryNormalizedTraceRelativeKernel N))
    (n : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernelPartial N beta n g h =
      inner ℝ
        ((specialUnitaryWilsonRelativeKernelPartialFeature
          N beta hbeta C n).feature g)
        ((specialUnitaryWilsonRelativeKernelPartialFeature
          N beta hbeta C n).feature h) :=
  (specialUnitaryWilsonRelativeKernelPartialFeature
    N beta hbeta C n).kernel_eq_inner g h

/-- Pull the relative Wilson kernel back along the positive-half holonomy of one
crossing plaquette. -/
def localCrossingWilsonKernel
    {X : Type}
    (N : ℕ)
    (beta : ℝ)
    (positiveHalfHolonomy : X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : X) : ℝ :=
  specialUnitaryWilsonRelativeKernel N beta
    (positiveHalfHolonomy x) (positiveHalfHolonomy y)

/-- The concrete crossing kernel pulled back along any positive-half holonomy
inherits the exact pointwise Wilson bounds. -/
theorem localCrossingWilsonKernel_mem_Icc
    {X : Type}
    {N : ℕ}
    (hN : 0 < N)
    {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (positiveHalfHolonomy : X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : X) :
    localCrossingWilsonKernel N beta positiveHalfHolonomy x y ∈
      Set.Icc (Real.exp (-2 * beta)) 1 := by
  exact specialUnitaryWilsonRelativeKernel_mem_Icc hN hbeta
    (positiveHalfHolonomy x) (positiveHalfHolonomy y)

/-- A Hilbert feature theorem for the relative `SU(N)` Wilson kernel pulls back
directly to a Hilbert feature theorem for one crossing plaquette. -/
noncomputable def localCrossingWilsonKernelFeature
    {X : Type}
    (N : ℕ)
    (beta : ℝ)
    (positiveHalfHolonomy : X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (C : RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernel N beta)) :
    RealHilbertKernelFeature X
      (localCrossingWilsonKernel N beta positiveHalfHolonomy) := by
  simpa [localCrossingWilsonKernel] using C.comap positiveHalfHolonomy

/-- The generated local feature has exactly the concrete crossing Wilson kernel
as its inner product. -/
theorem localCrossingWilsonKernelFeature_kernel_eq_inner
    {X : Type}
    (N : ℕ)
    (beta : ℝ)
    (positiveHalfHolonomy : X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (C : RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernel N beta))
    (x y : X) :
    localCrossingWilsonKernel N beta positiveHalfHolonomy x y =
      inner ℝ
        ((localCrossingWilsonKernelFeature N beta positiveHalfHolonomy C).feature x)
        ((localCrossingWilsonKernelFeature N beta positiveHalfHolonomy C).feature y) :=
  (localCrossingWilsonKernelFeature N beta positiveHalfHolonomy C).kernel_eq_inner x y

end

end MathlibAnalytic
end MGAP4D
