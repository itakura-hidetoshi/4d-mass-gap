import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Membership in the finite excitation sector is orthogonality to the vacuum. -/
theorem finite_wilson_mem_vacuumOrthogonal_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (vacuum x : E) :
    x ∈ finiteVacuumOrthogonal vacuum ↔ inner ℝ vacuum x = 0 := by
  simpa [finiteVacuumOrthogonal, finiteVacuumLine] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := vacuum) (v := x))

/-- A symmetric Hamiltonian with zero vacuum energy preserves the excitation sector. -/
theorem symmetric_zero_vacuum_preserves_vacuumOrthogonal
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (vacuum : E)
    (H : E →ₗ[ℝ] E)
    (hSymm : H.IsSymmetric)
    (hVacuum : H vacuum = 0)
    {x : E}
    (hx : x ∈ finiteVacuumOrthogonal vacuum) :
    H x ∈ finiteVacuumOrthogonal vacuum := by
  rw [finite_wilson_mem_vacuumOrthogonal_iff]
  calc
    inner ℝ vacuum (H x) = inner ℝ (H x) vacuum := real_inner_comm _ _
    _ = inner ℝ x (H vacuum) := hSymm x vacuum
    _ = 0 := by simp [hVacuum]

end

end MathlibAnalytic
end MGAP4D
