import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The real Euclidean carrier of the real and imaginary parts of all entries
of an `N × N` complex matrix.  The matrix indices are stored in transposed
order so that the inner product follows the diagonal expansion of
`Tr(g⁻¹h)` without a subsequent reindexing. -/
abbrev SpecialUnitaryMatrixRealFeatureSpace (N : ℕ) : Type :=
  EuclideanSpace ℝ ((Fin N × Fin N) × Bool)

/-- The realification of the defining matrix representation of `SU(N)`.
The `Bool` coordinate selects the real or imaginary part. -/
noncomputable def specialUnitaryMatrixRealFeature
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    SpecialUnitaryMatrixRealFeatureSpace N :=
  WithLp.toLp 2 fun q =>
    if q.2 then
      (U q.1.2 q.1.1).re
    else
      (U q.1.2 q.1.1).im

/-- The unnormalized real-trace relative kernel. -/
def specialUnitaryRealTraceRelativeKernel
    (N : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  (Matrix.trace
    ((g⁻¹ * h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re

/-- The real Euclidean inner product of the entry features is exactly the real
trace of the relative group element. -/
theorem specialUnitaryRealTraceRelativeKernel_eq_inner
    (N : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryRealTraceRelativeKernel N g h =
      inner ℝ
        (specialUnitaryMatrixRealFeature N g)
        (specialUnitaryMatrixRealFeature N h) := by
  classical
  symm
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [specialUnitaryMatrixRealFeature,
    specialUnitaryRealTraceRelativeKernel,
    Matrix.trace, Matrix.mul_apply,
    star_eq_conjTranspose, Complex.mul_re,
    Finset.sum_add_distrib]

/-- The unnormalized real-trace relative kernel has a concrete finite-dimensional
real Hilbert feature realization. -/
noncomputable def specialUnitaryRealTraceRelativeKernelFeature
    (N : ℕ) :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryRealTraceRelativeKernel N) where
  FeatureHilbert := SpecialUnitaryMatrixRealFeatureSpace N
  feature := specialUnitaryMatrixRealFeature N
  kernel_eq_inner := specialUnitaryRealTraceRelativeKernel_eq_inner N

/-- The normalized relative trace kernel is the nonnegative scalar multiple
`1/N` of the unnormalized real-trace kernel. -/
theorem specialUnitaryNormalizedTraceRelativeKernel_eq_scaled
    {N : ℕ}
    (hN : 0 < N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryNormalizedTraceRelativeKernel N g h =
      (1 / (N : ℝ)) * specialUnitaryRealTraceRelativeKernel N g h := by
  unfold specialUnitaryNormalizedTraceRelativeKernel
    specialUnitaryRealTraceRelativeKernel
  rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
  ring

/-- The normalized real-trace relative kernel has a concrete real Hilbert
feature realization obtained by the square-root `1/N` scaling of the defining
matrix representation. -/
noncomputable def specialUnitaryNormalizedTraceRelativeKernelFeature
    (N : ℕ)
    (hN : 0 < N) :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryNormalizedTraceRelativeKernel N) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hScale : 0 ≤ (1 / (N : ℝ)) := by positivity
  simpa [specialUnitaryNormalizedTraceRelativeKernel_eq_scaled hN] using
    RealHilbertKernelFeature.nonnegSMul
      (1 / (N : ℝ)) hScale
      (specialUnitaryRealTraceRelativeKernelFeature N)

/-- Consequently every finite Taylor approximation of the one-plaquette Wilson
relative kernel has an explicit finite completed-tensor-product Hilbert
feature, with no representation-theoretic hypothesis remaining. -/
noncomputable def specialUnitaryWilsonRelativeKernelPartialConcreteFeature
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernelPartial N beta degree) :=
  specialUnitaryWilsonRelativeKernelPartialFeature
    N beta hbeta
      (specialUnitaryNormalizedTraceRelativeKernelFeature N hN)
      degree

/-- The concrete finite Wilson feature realizes its partial kernel exactly. -/
theorem specialUnitaryWilsonRelativeKernelPartialConcrete_eq_inner
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernelPartial N beta degree g h =
      inner ℝ
        ((specialUnitaryWilsonRelativeKernelPartialConcreteFeature
          N hN beta hbeta degree).feature g)
        ((specialUnitaryWilsonRelativeKernelPartialConcreteFeature
          N hN beta hbeta degree).feature h) :=
  (specialUnitaryWilsonRelativeKernelPartialConcreteFeature
    N hN beta hbeta degree).kernel_eq_inner g h

end

end MathlibAnalytic
end MGAP4D
