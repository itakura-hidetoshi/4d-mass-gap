import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- The one-dimensional physical vacuum line. -/
def vacuumLine (P : D.OSPreHilbertData) : Submodule ℝ P.PhysicalHilbert :=
  ℝ ∙ P.vacuum

/-- The physical excitation sector, defined as the orthogonal complement of the vacuum line. -/
def vacuumOrthogonal (P : D.OSPreHilbertData) : Submodule ℝ P.PhysicalHilbert :=
  P.vacuumLineᗮ

/-- The complete Hilbert carrier of physical excitations. -/
abbrev VacuumOrthogonalHilbert (P : D.OSPreHilbertData) : Type :=
  P.vacuumOrthogonal

instance physicalYangMillsOSVacuumOrthogonalCompleteSpace
    (P : D.OSPreHilbertData) : CompleteSpace P.VacuumOrthogonalHilbert := by
  change CompleteSpace ↥P.vacuumLineᗮ
  exact Submodule.instOrthogonalCompleteSpace P.vacuumLine

/-- Membership in the excitation sector is orthogonality to the vacuum. -/
theorem mem_vacuumOrthogonal_iff
    (P : D.OSPreHilbertData) (psi : P.PhysicalHilbert) :
    psi ∈ P.vacuumOrthogonal ↔ inner ℝ P.vacuum psi = 0 := by
  simpa [vacuumOrthogonal, vacuumLine] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := P.vacuum) (v := psi))

/-- A normalized vacuum is not itself an excitation. -/
theorem vacuum_not_mem_vacuumOrthogonal
    (P : D.OSPreHilbertData) (hP : P.IsNormalized) :
    P.vacuum ∉ P.vacuumOrthogonal := by
  intro hvacuum
  have hinner : inner ℝ P.vacuum P.vacuum = 0 :=
    (P.mem_vacuumOrthogonal_iff P.vacuum).mp hvacuum
  have hzero : P.vacuum = 0 := inner_self_eq_zero.mp hinner
  have himpossible : (0 : ℝ) = 1 := by
    simpa [hzero] using P.norm_vacuum hP
  norm_num at himpossible

variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The vacuum regarded as a point of the graph-closed Hamiltonian domain. -/
def closedRightHamiltonianVacuumDomainPoint
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.closedRightHamiltonian.domain :=
  ⟨P.vacuum, by
    apply T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
    simpa only [T.rightHamiltonianLinearPMap_domain] using
      T.vacuum_mem_rightHamiltonianDomain⟩

/-- The graph-closed Hamiltonian annihilates the vacuum. -/
@[simp] theorem closedRightHamiltonian_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.closedRightHamiltonian T.closedRightHamiltonianVacuumDomainPoint = 0 := by
  let vacuumCore : T.rightHamiltonianLinearPMap.domain :=
    ⟨P.vacuum, by
      simpa only [T.rightHamiltonianLinearPMap_domain] using
        T.vacuum_mem_rightHamiltonianDomain⟩
  have hvalue :
      T.rightHamiltonianLinearPMap vacuumCore =
        T.closedRightHamiltonian T.closedRightHamiltonianVacuumDomainPoint :=
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2 rfl
  calc
    T.closedRightHamiltonian T.closedRightHamiltonianVacuumDomainPoint =
        T.rightHamiltonianLinearPMap vacuumCore := hvalue.symm
    _ = 0 := by
      simpa [vacuumCore] using T.rightHamiltonian_vacuum

/-- Formal self-adjointness and zero vacuum energy put the range in the excitation sector. -/
theorem closedRightHamiltonian_range_mem_vacuumOrthogonal
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff]
  calc
    inner ℝ P.vacuum (T.closedRightHamiltonian psi) =
        inner ℝ (T.closedRightHamiltonian psi) P.vacuum :=
      real_inner_comm _ _
    _ = inner ℝ (psi : P.PhysicalHilbert)
        (T.closedRightHamiltonian
          T.closedRightHamiltonianVacuumDomainPoint) :=
      hSymmetric psi T.closedRightHamiltonianVacuumDomainPoint
    _ = 0 := by rw [T.closedRightHamiltonian_vacuum, inner_zero_right]

/-- Self-adjointness supplies excitation-sector invariance. -/
theorem closedRightHamiltonian_range_mem_vacuumOrthogonal_of_isSelfAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi ∈ P.vacuumOrthogonal :=
  T.closedRightHamiltonian_range_mem_vacuumOrthogonal
    ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) psi

/-- The intersection domain inside the complete excitation Hilbert space. -/
def vacuumOrthogonalClosedRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Submodule ℝ P.VacuumOrthogonalHilbert where
  carrier := {psi | (psi : P.PhysicalHilbert) ∈ T.closedRightHamiltonian.domain}
  zero_mem' := T.closedRightHamiltonian.domain.zero_mem
  add_mem' := by
    intro x y hx hy
    change (x : P.PhysicalHilbert) + (y : P.PhysicalHilbert) ∈
      T.closedRightHamiltonian.domain
    exact T.closedRightHamiltonian.domain.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change c • (x : P.PhysicalHilbert) ∈ T.closedRightHamiltonian.domain
    exact T.closedRightHamiltonian.domain.smul_mem c hx

/-- A restricted-domain point viewed in the ambient closed-Hamiltonian domain. -/
def vacuumOrthogonalAmbientDomainPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
    T.closedRightHamiltonian.domain :=
  ⟨((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert), x.property⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
