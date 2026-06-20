import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The real Euclidean carrier of the real and imaginary parts of all entries
of an `N × N` complex matrix.  The matrix indices are stored in transposed
order so that the inner product follows the diagonal expansion of
`Tr(A* B)` without a subsequent reindexing. -/
abbrev SpecialUnitaryMatrixRealFeatureSpace (N : ℕ) : Type :=
  EuclideanSpace ℝ ((Fin N × Fin N) × Bool)

/-- Realification of a complex matrix by listing the real and imaginary parts
of all entries in transposed index order. -/
noncomputable def complexMatrixRealFeature
    (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    SpecialUnitaryMatrixRealFeatureSpace N :=
  WithLp.toLp 2 fun q =>
    if q.2 then
      (A q.1.2 q.1.1).re
    else
      (A q.1.2 q.1.1).im

/-- The Euclidean inner product of two realified matrices is the real part of
the Hilbert--Schmidt trace pairing. -/
theorem complexMatrixRealFeature_inner
    (N : ℕ)
    (A B : Matrix (Fin N) (Fin N) ℂ) :
    inner ℝ
        (complexMatrixRealFeature N A)
        (complexMatrixRealFeature N B) =
      (Matrix.trace (A.conjTranspose * B)).re := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [complexMatrixRealFeature, Matrix.trace, Matrix.mul_apply,
    Complex.mul_re, Finset.sum_add_distrib, mul_comm]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [RCLike.inner_apply]

/-- The realification of the defining matrix representation of `SU(N)`. -/
noncomputable def specialUnitaryMatrixRealFeature
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    SpecialUnitaryMatrixRealFeatureSpace N :=
  complexMatrixRealFeature N
    (U : Matrix (Fin N) (Fin N) ℂ)

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
  change
    (Matrix.trace
      ((g : Matrix (Fin N) (Fin N) ℂ).conjTranspose *
        (h : Matrix (Fin N) (Fin N) ℂ))).re =
      inner ℝ
        (complexMatrixRealFeature N
          (g : Matrix (Fin N) (Fin N) ℂ))
        (complexMatrixRealFeature N
          (h : Matrix (Fin N) (Fin N) ℂ))
  exact (complexMatrixRealFeature_inner N
    (g : Matrix (Fin N) (Fin N) ℂ)
    (h : Matrix (Fin N) (Fin N) ℂ)).symm

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

/-- The normalized relative trace kernel is the scalar multiple `1/N` of the
unnormalized real-trace kernel. -/
theorem specialUnitaryNormalizedTraceRelativeKernel_eq_scaled
    (N : ℕ)
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
  let C := RealHilbertKernelFeature.nonnegSMul
    (1 / (N : ℝ)) hScale
    (specialUnitaryRealTraceRelativeKernelFeature N)
  exact
    { FeatureHilbert := C.FeatureHilbert
      featureNormedAddCommGroup := C.featureNormedAddCommGroup
      featureInnerProductSpace := C.featureInnerProductSpace
      featureCompleteSpace := C.featureCompleteSpace
      feature := C.feature
      kernel_eq_inner := by
        intro g h
        rw [specialUnitaryNormalizedTraceRelativeKernel_eq_scaled]
        exact C.kernel_eq_inner g h }

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
