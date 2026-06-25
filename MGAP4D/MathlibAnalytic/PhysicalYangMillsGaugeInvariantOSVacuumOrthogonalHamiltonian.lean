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

/-- The physical excitation sector `Ω⊥`, defined as the orthogonal complement of
 the vacuum line in the completed Osterwalder--Schrader Hilbert space. -/
def vacuumOrthogonal (P : D.OSPreHilbertData) : Submodule ℝ P.PhysicalHilbert :=
  P.vacuumLineᗮ

/-- The complete Hilbert carrier of physical excitations. -/
abbrev VacuumOrthogonalHilbert (P : D.OSPreHilbertData) : Type :=
  P.vacuumOrthogonal

/-- Mathlib's orthogonal-complement construction makes `Ω⊥` complete. -/
instance physicalYangMillsOSVacuumOrthogonalCompleteSpace
    (P : D.OSPreHilbertData) :
    CompleteSpace P.VacuumOrthogonalHilbert := by
  change CompleteSpace ↥P.vacuumLineᗮ
  exact Submodule.instOrthogonalCompleteSpace P.vacuumLine

/-- Membership in the physical excitation sector is exactly orthogonality to the
 normalized OS vacuum. -/
theorem mem_vacuumOrthogonal_iff
    (P : D.OSPreHilbertData) (psi : P.PhysicalHilbert) :
    psi ∈ P.vacuumOrthogonal ↔ inner ℝ P.vacuum psi = 0 := by
  simpa [vacuumOrthogonal, vacuumLine] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := P.vacuum) (v := psi))

/-- A normalized OS vacuum is not itself an excitation. -/
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

/-- The graph-closed Hamiltonian still annihilates the physical vacuum. -/
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

/-- Formal self-adjointness and zero vacuum energy imply that the range of the
 closed Hamiltonian lies in `Ω⊥`.  In particular, `Ω⊥` is invariant. -/
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

/-- Self-adjointness supplies the invariant excitation-sector conclusion without
 retaining a separate symmetry hypothesis. -/
theorem closedRightHamiltonian_range_mem_vacuumOrthogonal_of_isSelfAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi ∈ P.vacuumOrthogonal :=
  T.closedRightHamiltonian_range_mem_vacuumOrthogonal
    ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) psi

/-- The domain `D(H̄) ∩ Ω⊥`, represented inside the complete excitation Hilbert
 space. -/
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

/-- A restricted-domain point viewed in the ambient closed Hamiltonian domain. -/
def vacuumOrthogonalAmbientDomainPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
    T.closedRightHamiltonian.domain :=
  ⟨((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert), x.property⟩

/-- The closed Hamiltonian action bundled as a linear map from
 `D(H̄) ∩ Ω⊥` into `Ω⊥`. -/
def vacuumOrthogonalClosedRightHamiltonianLinearMap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    T.vacuumOrthogonalClosedRightHamiltonianDomain →ₗ[ℝ]
      P.VacuumOrthogonalHilbert where
  toFun := fun x =>
    ⟨T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint x),
      T.closedRightHamiltonian_range_mem_vacuumOrthogonal hSymmetric
        (T.vacuumOrthogonalAmbientDomainPoint x)⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simpa [vacuumOrthogonalAmbientDomainPoint] using
      T.closedRightHamiltonian.toFun.map_add
        (T.vacuumOrthogonalAmbientDomainPoint x)
        (T.vacuumOrthogonalAmbientDomainPoint y)
  map_smul' := by
    intro c x
    apply Subtype.ext
    simpa [vacuumOrthogonalAmbientDomainPoint] using
      T.closedRightHamiltonian.toFun.map_smul c
        (T.vacuumOrthogonalAmbientDomainPoint x)

/-- The actual graph-closed OS Hamiltonian restricted to the physical excitation
 sector `Ω⊥`. -/
def vacuumOrthogonalClosedRightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    P.VacuumOrthogonalHilbert →ₗ.[ℝ] P.VacuumOrthogonalHilbert :=
  { domain := T.vacuumOrthogonalClosedRightHamiltonianDomain
    toFun := T.vacuumOrthogonalClosedRightHamiltonianLinearMap hSymmetric }

/-- The restricted Hamiltonian has exactly the intersection domain
 `D(H̄) ∩ Ω⊥`. -/
@[simp] theorem vacuumOrthogonalClosedRightHamiltonian_domain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain =
      T.vacuumOrthogonalClosedRightHamiltonianDomain :=
  rfl

/-- After inclusion into the physical Hilbert space, the restricted action is
 exactly the ambient graph-closed Hamiltonian action. -/
@[simp] theorem vacuumOrthogonalClosedRightHamiltonian_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (x : (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain) :
    (((T.vacuumOrthogonalClosedRightHamiltonian hSymmetric x :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint x) :=
  rfl

/-- Symmetry of the ambient closed Hamiltonian descends to the actual restricted
 excitation-sector operator. -/
theorem vacuumOrthogonalClosedRightHamiltonian_isFormalAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).IsFormalAdjoint
      (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric) := by
  intro x y
  change inner ℝ
      (T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint x))
      ((y : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert) =
    inner ℝ
      ((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert)
      (T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint y))
  exact hSymmetric
    (T.vacuumOrthogonalAmbientDomainPoint x)
    (T.vacuumOrthogonalAmbientDomainPoint y)

/-- The finite-volume transfer gap becomes a positive Rayleigh lower bound for
 the actual closed Hamiltonian restricted to `Ω⊥`. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalClosedRightHamiltonian_gap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (x : (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain) :
    G.mass * ‖((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric x)
        ((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
          P.VacuumOrthogonalHilbert) := by
  have hxOrthogonal :
      inner ℝ
          (((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
          P.vacuum = 0 := by
    rw [real_inner_comm]
    exact (P.mem_vacuumOrthogonal_iff _).mp
      ((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert).property
  simpa [vacuumOrthogonalClosedRightHamiltonian,
    vacuumOrthogonalClosedRightHamiltonianLinearMap] using
    G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      T hP (T.vacuumOrthogonalAmbientDomainPoint x) hxOrthogonal

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
