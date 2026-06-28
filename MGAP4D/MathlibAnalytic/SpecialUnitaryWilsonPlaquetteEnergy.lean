import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryMatrixTraceFormula
import Mathlib.Topology.Instances.Matrix

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The conventional Wilson plaquette energy on `SU(N)`. -/
def specialUnitaryWilsonPlaquetteEnergy
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  1 -
    (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re /
      (N : ℝ)

/-- The conventional Wilson plaquette energy agrees with one minus the
normalized special-unitary real trace. -/
theorem specialUnitaryWilsonPlaquetteEnergy_eq
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N U =
      1 - normalizedSpecialUnitaryRealTrace N U := by
  rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div]
  rfl

/-- Standard `SU(N)` Wilson plaquette energy is nonnegative for positive rank. -/
theorem specialUnitaryWilsonPlaquetteEnergy_nonneg
    {N : ℕ}
    (hN : 0 < N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 ≤ specialUnitaryWilsonPlaquetteEnergy N U := by
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  linarith [(normalizedSpecialUnitaryRealTrace_mem_Icc hN U).2]

/-- Standard `SU(N)` Wilson plaquette energy is at most two. -/
theorem specialUnitaryWilsonPlaquetteEnergy_le_two
    {N : ℕ}
    (hN : 0 < N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N U ≤ 2 := by
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  linarith [(normalizedSpecialUnitaryRealTrace_mem_Icc hN U).1]

/-- Standard `SU(N)` Wilson plaquette energy takes values in `[0,2]`. -/
theorem specialUnitaryWilsonPlaquetteEnergy_mem_Icc
    {N : ℕ}
    (hN : 0 < N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N U ∈ Set.Icc (0 : ℝ) 2 :=
  ⟨specialUnitaryWilsonPlaquetteEnergy_nonneg hN U,
    specialUnitaryWilsonPlaquetteEnergy_le_two hN U⟩

/-- Standard `SU(N)` Wilson plaquette energy is continuous. -/
theorem continuous_specialUnitaryWilsonPlaquetteEnergy
    (N : ℕ) :
    Continuous (specialUnitaryWilsonPlaquetteEnergy N) := by
  unfold specialUnitaryWilsonPlaquetteEnergy
  fun_prop

end

end MathlibAnalytic
end MGAP4D
