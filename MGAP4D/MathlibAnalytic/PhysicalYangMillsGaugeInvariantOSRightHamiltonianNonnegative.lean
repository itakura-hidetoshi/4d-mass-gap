import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageGeneratorDomain
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A completed physical Euclidean-time contraction cannot increase its real
pairing with the original vector. -/
theorem physicalOperator_inner_le_self
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    ⟪T.toPhysicalSemigroup.operator t psi, psi⟫_ℝ ≤ ⟪psi, psi⟫_ℝ := by
  calc
    ⟪T.toPhysicalSemigroup.operator t psi, psi⟫_ℝ ≤
        ‖T.toPhysicalSemigroup.operator t psi‖ * ‖psi‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖psi‖ * ‖psi‖ :=
      mul_le_mul_of_nonneg_right
        (T.physicalOperator_norm_le t psi) (norm_nonneg psi)
    _ = ⟪psi, psi⟫_ℝ :=
      (real_inner_self_eq_norm_mul_norm psi).symm

/-- Every positive-time generator difference quotient has nonpositive real
pairing with the initial vector. -/
theorem rightDifferenceQuotient_inner_nonpos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) (ht : 0 < t) :
    ⟪T.rightDifferenceQuotient psi t, psi⟫_ℝ ≤ 0 := by
  have hsub :
      ⟪T.toPhysicalSemigroup.operator t psi - psi, psi⟫_ℝ ≤ 0 := by
    rw [inner_sub_left]
    exact sub_nonpos.mpr (T.physicalOperator_inner_le_self t psi)
  have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
  have hinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr htReal.le
  have hmul := mul_nonpos_of_nonneg_of_nonpos hinv hsub
  simpa [rightDifferenceQuotient, real_inner_smul_left] using hmul

/-- The right infinitesimal generator of a strongly continuous contraction
semigroup is dissipative on its canonical domain. -/
theorem rightGenerator_inner_nonpos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    ⟪T.rightGenerator psi, (psi : P.PhysicalHilbert)⟫_ℝ ≤ 0 := by
  have hgenerator := T.rightGenerator_hasRightGeneratorValue psi
  unfold HasRightGeneratorValue at hgenerator
  have hinner :
      Tendsto
        (fun t : NNReal =>
          ⟪T.rightDifferenceQuotient (psi : P.PhysicalHilbert) t,
            (psi : P.PhysicalHilbert)⟫_ℝ)
        (nhdsWithin 0 (Ioi 0))
        (nhds ⟪T.rightGenerator psi, (psi : P.PhysicalHilbert)⟫_ℝ) := by
    exact hgenerator.inner tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hinner tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact T.rightDifferenceQuotient_inner_nonpos
    (psi : P.PhysicalHilbert) t ht

/-- In the Euclidean convention `T_t = exp (-t H)`, the canonical right
Hamiltonian has a nonnegative quadratic form on its dense domain.  This is an
accretivity statement only; it does not assert symmetry or self-adjointness. -/
theorem rightHamiltonian_inner_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    0 ≤ ⟪T.rightHamiltonian psi, (psi : P.PhysicalHilbert)⟫_ℝ := by
  rw [T.rightHamiltonian_apply, inner_neg_left]
  exact neg_nonneg.mpr (T.rightGenerator_inner_nonpos psi)

/-- The right Hamiltonian is densely defined and has nonnegative quadratic
form on that domain. -/
theorem rightHamiltonian_dense_nonnegative
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Dense (T.rightGeneratorDomain : Set P.PhysicalHilbert) ∧
      ∀ psi : T.rightGeneratorDomain,
        0 ≤ ⟪T.rightHamiltonian psi, (psi : P.PhysicalHilbert)⟫_ℝ :=
  ⟨T.rightHamiltonianDomain_dense, T.rightHamiltonian_inner_nonneg⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
