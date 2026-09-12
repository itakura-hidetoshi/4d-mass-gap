import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The normalized real trace on `SU(N)` is cyclic on two factors.  This is the
scalar trace identity used to rotate a fixed boundary incidence to the first
slot of a temporal plaquette holonomy. -/
theorem normalizedSpecialUnitaryRealTrace_mul_cycle
    {N : ℕ}
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N (g * h) =
      normalizedSpecialUnitaryRealTrace N (h * g) := by
  rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div,
    normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
  congr 1
  apply congrArg Complex.re
  change Matrix.trace
      ((g : Matrix (Fin N) (Fin N) ℂ) *
        (h : Matrix (Fin N) (Fin N) ℂ)) =
    Matrix.trace
      ((h : Matrix (Fin N) (Fin N) ℂ) *
        (g : Matrix (Fin N) (Fin N) ℂ))
  calc
    Matrix.trace
        ((g : Matrix (Fin N) (Fin N) ℂ) *
          (h : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.trace
        ((1 : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ) *
          (h : Matrix (Fin N) (Fin N) ℂ)) := by simp
    _ = Matrix.trace
        ((h : Matrix (Fin N) (Fin N) ℂ) *
          (1 : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ)) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace
        ((h : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ)) := by simp

end

end MathlibAnalytic
end MGAP4D
