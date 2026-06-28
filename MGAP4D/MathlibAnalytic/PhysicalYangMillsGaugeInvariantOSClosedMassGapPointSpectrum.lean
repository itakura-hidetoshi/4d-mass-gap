import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A symmetric closed OS Hamiltonian with a positive vacuum-sector Rayleigh
bound has no nonzero eigenvector with eigenvalue in the open interval `(0,mass)`.

Symmetry first makes every positive-energy eigenvector orthogonal to the vacuum,
because the vacuum lies in the closed domain and is annihilated by the closed
Hamiltonian.  The closed-domain mass-gap inequality then contradicts an
eigenvalue strictly below the transferred mass unless the vector vanishes. -/
theorem VacuumSemigroupGapSlope.closedRightHamiltonian_no_eigenvector_in_open_mass_gap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_mass : lambda < G.mass)
    (psi : T.closedRightHamiltonian.domain)
    (hEigen :
      T.closedRightHamiltonian psi =
        lambda • (psi : P.PhysicalHilbert)) :
    (psi : P.PhysicalHilbert) = 0 := by
  let vacuumCore : T.rightHamiltonianLinearPMap.domain :=
    ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩
  let vacuumClosed : T.closedRightHamiltonian.domain :=
    Submodule.inclusion
      T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1 vacuumCore
  have hvacuumClosed_coe :
      (vacuumClosed : P.PhysicalHilbert) = P.vacuum := by
    rfl
  have hvacuumClosed_value :
      T.closedRightHamiltonian vacuumClosed = 0 := by
    have hle := LinearPMap.apply_comp_inclusion
      T.rightHamiltonianLinearPMap_le_closedRightHamiltonian vacuumCore
    calc
      T.closedRightHamiltonian vacuumClosed =
          T.rightHamiltonianLinearPMap vacuumCore := by
        exact hle.symm
      _ = 0 := by
        simpa [vacuumCore] using T.rightHamiltonian_vacuum
  have hSymmetryPairing := hSymmetric psi vacuumClosed
  have horthogonal_mul :
      lambda * inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 := by
    rw [hEigen, hvacuumClosed_coe, hvacuumClosed_value,
      real_inner_smul_left, inner_zero_right] at hSymmetryPairing
    exact hSymmetryPairing
  have horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 := by
    exact (mul_eq_zero.mp horthogonal_mul).resolve_left
      (ne_of_gt hlambda_pos)
  have hgap :=
    G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      T hP psi horthogonal
  rw [hEigen, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hgap
  have hnormSq : ‖(psi : P.PhysicalHilbert)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖(psi : P.PhysicalHilbert)‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- The same point-spectrum exclusion, stated from self-adjointness rather than
formal symmetry. -/
theorem VacuumSemigroupGapSlope.closedRightHamiltonian_no_eigenvector_in_open_mass_gap_of_selfAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSelfAdjoint : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_mass : lambda < G.mass)
    (psi : T.closedRightHamiltonian.domain)
    (hEigen :
      T.closedRightHamiltonian psi =
        lambda • (psi : P.PhysicalHilbert)) :
    (psi : P.PhysicalHilbert) = 0 :=
  G.closedRightHamiltonian_no_eigenvector_in_open_mass_gap
    T hP
    ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp
      hSelfAdjoint)
    hlambda_pos hlambda_mass psi hEigen

/-- A uniform finite-volume transfer gap therefore excludes every nonzero point
of the closed continuum Hamiltonian spectrum in `(0,mass)` at the eigenvector
level. -/
theorem FiniteVolumeVacuumGapTransfer.closedRightHamiltonian_no_eigenvector_in_open_mass_gap_of_selfAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelfAdjoint : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_mass : lambda < G.mass)
    (psi : T.closedRightHamiltonian.domain)
    (hEigen :
      T.closedRightHamiltonian psi =
        lambda • (psi : P.PhysicalHilbert)) :
    (psi : P.PhysicalHilbert) = 0 :=
  G.toVacuumSemigroupGapSlope
    |>.closedRightHamiltonian_no_eigenvector_in_open_mass_gap_of_selfAdjoint
      T hP hSelfAdjoint hlambda_pos hlambda_mass psi hEigen

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
