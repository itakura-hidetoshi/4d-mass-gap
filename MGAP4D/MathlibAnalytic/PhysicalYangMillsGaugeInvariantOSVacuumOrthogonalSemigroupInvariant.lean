import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeContraction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace InnerProduct LinearPMap

/-- A contraction fixing a unit vector also fixes that vector under its adjoint.

This elementary Hilbert-space fact is the key point allowing the physical
positive-time semigroup to preserve the vacuum-orthogonal sector without any
self-adjointness assumption on the bounded semigroup operators. -/
private theorem adjoint_fixes_unit_of_opNorm_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (Omega : E)
    (hA : ‖A‖ ≤ 1) (hOmega : ‖Omega‖ = 1) (hfix : A Omega = Omega) :
    A† Omega = Omega := by
  have hnorm : ‖A† Omega‖ ≤ 1 := by
    calc
      ‖A† Omega‖ ≤ ‖A†‖ * ‖Omega‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A‖ * 1 := by
        rw [LinearIsometryEquiv.norm_map, hOmega]
      _ ≤ 1 := by simpa using hA
  have hadjOmega : inner ℝ (A† Omega) Omega = 1 := by
    calc
      inner ℝ (A† Omega) Omega = inner ℝ Omega (A Omega) :=
        A.adjoint_inner_left Omega Omega
      _ = inner ℝ Omega Omega := by rw [hfix]
      _ = 1 := by
        rw [real_inner_self_eq_norm_sq, hOmega]
        norm_num
  have hOmegaAdj : inner ℝ Omega (A† Omega) = 1 := by
    rw [real_inner_comm]
    exact hadjOmega
  have hOmegaSelf : inner ℝ Omega Omega = 1 := by
    rw [real_inner_self_eq_norm_sq, hOmega]
    norm_num
  have hAdjSelf : inner ℝ (A† Omega) (A† Omega) ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg (A† Omega)]
  have hdiff_le :
      inner ℝ (A† Omega - Omega) (A† Omega - Omega) ≤ 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    nlinarith
  have hdiff_nonneg :
      0 ≤ inner ℝ (A† Omega - Omega) (A† Omega - Omega) := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  have hdiff_zero :
      inner ℝ (A† Omega - Omega) (A† Omega - Omega) = 0 :=
    le_antisymm hdiff_le hdiff_nonneg
  have hsub : A† Omega - Omega = 0 :=
    (inner_self_eq_zero.mp hdiff_zero)
  exact sub_eq_zero.mp hsub

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PhysicalSemigroup

/-- Every positive-time physical contraction preserving the normalized vacuum
also preserves the vacuum-orthogonal excitation sector.

No bounded-operator self-adjointness is assumed: contractivity and exact vacuum
fixing force the adjoint to fix the vacuum, after which the adjoint identity
transports vacuum orthogonality. -/
theorem operator_mem_vacuumOrthogonal
    (T : P.PhysicalSemigroup) (hP : P.IsNormalized) (t : NNReal)
    {psi : P.PhysicalHilbert} (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.operator t psi ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff] at hpsi ⊢
  have hadjFix : (T.operator t)† P.vacuum = P.vacuum :=
    adjoint_fixes_unit_of_opNorm_le_one
      (T.operator t) P.vacuum (T.opNorm_le t) (P.norm_vacuum hP)
      (T.fixes_vacuum t)
  calc
    inner ℝ P.vacuum (T.operator t psi) =
        inner ℝ ((T.operator t)† P.vacuum) psi := by
      symm
      exact (T.operator t).adjoint_inner_left psi P.vacuum
    _ = inner ℝ P.vacuum psi := by rw [hadjFix]
    _ = 0 := hpsi

end PhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
