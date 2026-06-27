import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
import Mathlib.Tactic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A positive transferred excitation gap makes every zero-energy vector of the
closed OS Hamiltonian a vacuum multiple.

The proof orthogonalizes an arbitrary zero-energy domain vector by subtracting
its vacuum coefficient.  The vacuum is itself in the closed-Hamiltonian domain
and has zero energy, so the orthogonalized vector still has zero energy.  The
transferred Rayleigh lower bound and positivity of the mass then force its norm
to vanish. -/
theorem FiniteVolumeVacuumGapTransfer.closedRightHamiltonian_eq_inner_smul_vacuum_of_eq_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hzero : T.closedRightHamiltonian psi = 0) :
    (psi : P.PhysicalHilbert) =
      (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  let c : ℝ := inner ℝ (psi : P.PhysicalHilbert) P.vacuum
  let vacuumDomain : T.closedRightHamiltonian.domain :=
    T.closedRightHamiltonianVacuumDomainPoint
  let psiOrth : T.closedRightHamiltonian.domain :=
    psi - c • vacuumDomain
  have hvacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  have hpsiOrthogonal :
      inner ℝ (psiOrth : P.PhysicalHilbert) P.vacuum = 0 := by
    change inner ℝ
      ((psi : P.PhysicalHilbert) - c • P.vacuum) P.vacuum = 0
    rw [inner_sub_left, real_inner_smul_left, hvacuumInner, mul_one]
    exact sub_self c
  have hpsiOrthogonalEnergy : T.closedRightHamiltonian psiOrth = 0 := by
    change T.closedRightHamiltonian (psi - c • vacuumDomain) = 0
    rw [map_sub, map_smul, hzero, T.closedRightHamiltonian_vacuum,
      smul_zero, sub_zero]
  have hgap :=
    G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      T hP psiOrth hpsiOrthogonal
  have hnonpos :
      G.mass * ‖(psiOrth : P.PhysicalHilbert)‖ ^ 2 ≤ 0 := by
    simpa only [hpsiOrthogonalEnergy, zero_inner] using hgap
  have hnorm : ‖(psiOrth : P.PhysicalHilbert)‖ = 0 := by
    nlinarith [G.mass_pos, sq_nonneg ‖(psiOrth : P.PhysicalHilbert)‖]
  have hpsiOrthZero : (psiOrth : P.PhysicalHilbert) = 0 :=
    norm_eq_zero.mp hnorm
  have hsub :
      (psi : P.PhysicalHilbert) - c • P.vacuum = 0 := by
    simpa only [psiOrth, vacuumDomain] using hpsiOrthZero
  simpa only [c] using sub_eq_zero.mp hsub

/-- Under the transferred positive mass gap, the zero eigenspace of the closed
OS Hamiltonian is exactly the one-dimensional vacuum direction.  The displayed
coefficient is canonical because the normalized vacuum has unit norm. -/
theorem FiniteVolumeVacuumGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  constructor
  · exact G.closedRightHamiltonian_eq_inner_smul_vacuum_of_eq_zero
      T hP psi
  · intro hpsi
    let c : ℝ := inner ℝ (psi : P.PhysicalHilbert) P.vacuum
    have hpsiDomain :
        psi = c • T.closedRightHamiltonianVacuumDomainPoint := by
      apply Subtype.ext
      simpa only [c] using hpsi
    rw [hpsiDomain, map_smul, T.closedRightHamiltonian_vacuum, smul_zero]

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
