import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteRKHS
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For positive matrix size and nonnegative coupling, the exact one-plaquette
Wilson relative kernel has a real Hilbert feature realization.  The feature
space is mathlib's Moore--Aronszajn reproducing-kernel Hilbert space generated
by the exact positive-semidefinite kernel. -/
noncomputable def specialUnitaryWilsonRelativeKernelFeature
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernel N beta) :=
  (specialUnitaryWilsonRelativeKernel_positiveSemidefiniteCertificate
    N hN beta hbeta).toHilbertFeature

/-- The exact Wilson relative kernel is the inner product of its RKHS kernel
features. -/
theorem specialUnitaryWilsonRelativeKernelFeature_kernel_eq_inner
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta g h =
      inner ℝ
        ((specialUnitaryWilsonRelativeKernelFeature
          N hN beta hbeta).feature g)
        ((specialUnitaryWilsonRelativeKernelFeature
          N hN beta hbeta).feature h) :=
  (specialUnitaryWilsonRelativeKernelFeature
    N hN beta hbeta).kernel_eq_inner g h

/-- Pull the exact Wilson RKHS feature back along the positive-half holonomy of
one crossing plaquette. -/
noncomputable def localCrossingWilsonKernelConcreteFeature
    {X : Type}
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (positiveHalfHolonomy : X → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    RealHilbertKernelFeature X
      (localCrossingWilsonKernel N beta positiveHalfHolonomy) :=
  localCrossingWilsonKernelFeature
    N beta positiveHalfHolonomy
      (specialUnitaryWilsonRelativeKernelFeature N hN beta hbeta)

/-- The concrete one-crossing-plaquette Wilson kernel is exactly the inner
product of the pulled-back RKHS features. -/
theorem localCrossingWilsonKernelConcreteFeature_kernel_eq_inner
    {X : Type}
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (positiveHalfHolonomy : X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : X) :
    localCrossingWilsonKernel N beta positiveHalfHolonomy x y =
      inner ℝ
        ((localCrossingWilsonKernelConcreteFeature
          N hN beta hbeta positiveHalfHolonomy).feature x)
        ((localCrossingWilsonKernelConcreteFeature
          N hN beta hbeta positiveHalfHolonomy).feature y) :=
  (localCrossingWilsonKernelConcreteFeature
    N hN beta hbeta positiveHalfHolonomy).kernel_eq_inner x y

end

end MathlibAnalytic
end MGAP4D
