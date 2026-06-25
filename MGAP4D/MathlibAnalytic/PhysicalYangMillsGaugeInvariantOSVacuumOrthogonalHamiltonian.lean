import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
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

/-- The closed Hamiltonian action bundled from the excitation-domain intersection into the excitation sector. -/
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
    have hDomain :
        T.vacuumOrthogonalAmbientDomainPoint (c • x) =
          c • T.vacuumOrthogonalAmbientDomainPoint x := by
      apply Subtype.ext
      rfl
    change T.closedRightHamiltonian
        (T.vacuumOrthogonalAmbientDomainPoint (c • x)) =
      c • T.closedRightHamiltonian
        (T.vacuumOrthogonalAmbientDomainPoint x)
    rw [hDomain]
    exact T.closedRightHamiltonian.toFun.map_smul c
      (T.vacuumOrthogonalAmbientDomainPoint x)

/-- The graph-closed OS Hamiltonian restricted to the physical excitation sector. -/
def vacuumOrthogonalClosedRightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    P.VacuumOrthogonalHilbert →ₗ.[ℝ] P.VacuumOrthogonalHilbert :=
  { domain := T.vacuumOrthogonalClosedRightHamiltonianDomain
    toFun := T.vacuumOrthogonalClosedRightHamiltonianLinearMap hSymmetric }

@[simp] theorem vacuumOrthogonalClosedRightHamiltonian_domain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain =
      T.vacuumOrthogonalClosedRightHamiltonianDomain :=
  rfl

@[simp] theorem vacuumOrthogonalClosedRightHamiltonian_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (x : (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain) :
    (((T.vacuumOrthogonalClosedRightHamiltonian hSymmetric x :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint x) :=
  rfl

/-- Ambient symmetry descends to the restricted excitation-sector Hamiltonian. -/
theorem vacuumOrthogonalClosedRightHamiltonian_isFormalAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).IsFormalAdjoint
      (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric) := by
  intro x y
  change inner ℝ
      (T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint x))
      (((y : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) =
    inner ℝ
      (((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
      (T.closedRightHamiltonian (T.vacuumOrthogonalAmbientDomainPoint y))
  exact hSymmetric
    (T.vacuumOrthogonalAmbientDomainPoint x)
    (T.vacuumOrthogonalAmbientDomainPoint y)

/-- A finite-volume transfer gap becomes the restricted closed-Hamiltonian Rayleigh lower bound. -/
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
