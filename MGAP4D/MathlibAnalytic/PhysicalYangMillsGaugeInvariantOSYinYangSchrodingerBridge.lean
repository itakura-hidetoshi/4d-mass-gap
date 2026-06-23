import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianSemigroupCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

/-- The real two-component carrier underlying a complex physical state.
The first component is the Yang component and the second component is the Yin
component.  This is only a realification layer; it does not assert that the
right Hamiltonian is self-adjoint. -/
abbrev YinYangPhysicalState (P : D.OSPreHilbertData) :=
  P.PhysicalHilbert × P.PhysicalHilbert

/-- Embed a physical vector as a pure Yang component. -/
def yangEmbedding (P : D.OSPreHilbertData) :
    P.PhysicalHilbert →ₗ[ℝ] P.YinYangPhysicalState where
  toFun psi := (psi, 0)
  map_add' psi phi := by
    ext <;> simp
  map_smul' r psi := by
    ext <;> simp

/-- Embed a physical vector as a pure Yin component. -/
def yinEmbedding (P : D.OSPreHilbertData) :
    P.PhysicalHilbert →ₗ[ℝ] P.YinYangPhysicalState where
  toFun psi := (0, psi)
  map_add' psi phi := by
    ext <;> simp
  map_smul' r psi := by
    ext <;> simp

/-- The canonical complex structure on the real Yang-Yin pair.
It represents multiplication by `i` under the identification
`(yang, yin) ↔ yang + i yin`. -/
def yinYangComplexStructure (P : D.OSPreHilbertData) :
    P.YinYangPhysicalState →ₗ[ℝ] P.YinYangPhysicalState where
  toFun state := (-state.2, state.1)
  map_add' state₁ state₂ := by
    ext <;> simp
  map_smul' r state := by
    ext <;> simp

@[simp] theorem yinYangComplexStructure_apply
    (P : D.OSPreHilbertData) (state : P.YinYangPhysicalState) :
    P.yinYangComplexStructure state = (-state.2, state.1) :=
  rfl

/-- Two Yin-Yang quarter-turns give sign reversal: `J² = -I`. -/
@[simp] theorem yinYangComplexStructure_sq_apply
    (P : D.OSPreHilbertData) (state : P.YinYangPhysicalState) :
    P.yinYangComplexStructure (P.yinYangComplexStructure state) = -state := by
  rcases state with ⟨yang, yin⟩
  simp [yinYangComplexStructure]

/-- A pure Yang component turns into the corresponding pure Yin component. -/
@[simp] theorem yinYangComplexStructure_yangEmbedding
    (P : D.OSPreHilbertData) (psi : P.PhysicalHilbert) :
    P.yinYangComplexStructure (P.yangEmbedding psi) = P.yinEmbedding psi := by
  rfl

/-- A pure Yin component turns into the negative pure Yang component. -/
@[simp] theorem yinYangComplexStructure_yinEmbedding
    (P : D.OSPreHilbertData) (psi : P.PhysicalHilbert) :
    P.yinYangComplexStructure (P.yinEmbedding psi) = -P.yangEmbedding psi := by
  ext <;> simp [yinYangComplexStructure, yinEmbedding, yangEmbedding]

namespace StronglyContinuousPhysicalSemigroup

/-- The two-component domain on which both real components admit the canonical
right Hamiltonian value. -/
abbrev RightHamiltonianYinYangDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :=
  T.rightGeneratorDomain × T.rightGeneratorDomain

/-- Apply the right Hamiltonian independently to the Yang and Yin components. -/
noncomputable def rightHamiltonianYinYangPair
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.RightHamiltonianYinYangDomain →ₗ[ℝ] P.YinYangPhysicalState where
  toFun state :=
    (T.rightHamiltonian state.1, T.rightHamiltonian state.2)
  map_add' state₁ state₂ := by
    ext <;> simp
  map_smul' r state := by
    ext <;> simp

@[simp] theorem rightHamiltonianYinYangPair_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (state : T.RightHamiltonianYinYangDomain) :
    T.rightHamiltonianYinYangPair state =
      (T.rightHamiltonian state.1, T.rightHamiltonian state.2) :=
  rfl

/-- The algebraic Schrödinger vector field on the real two-component domain.
With `J(y, n) = (-n, y)`, the equation `i ψ' = H ψ` becomes
`(y', n') = (H n, -H y)`, hence the defining sign is `-JH`.  This definition
precedes and does not claim self-adjoint real-time evolution. -/
noncomputable def rightSchrodingerVectorField
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.RightHamiltonianYinYangDomain →ₗ[ℝ] P.YinYangPhysicalState :=
  -(P.yinYangComplexStructure.comp T.rightHamiltonianYinYangPair)

/-- The two real component equations underlying the Schrödinger sign
convention. -/
@[simp] theorem rightSchrodingerVectorField_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (state : T.RightHamiltonianYinYangDomain) :
    T.rightSchrodingerVectorField state =
      (T.rightHamiltonian state.2, -T.rightHamiltonian state.1) := by
  rcases state with ⟨yang, yin⟩
  ext <;> simp [rightSchrodingerVectorField,
    rightHamiltonianYinYangPair, yinYangComplexStructure]

/-- The doubled physical vacuum belongs to the two-component Hamiltonian
domain. -/
noncomputable def yinYangVacuumDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.RightHamiltonianYinYangDomain :=
  (⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩,
    ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩)

/-- Both Hamiltonian components vanish on the doubled vacuum. -/
@[simp] theorem rightHamiltonianYinYangPair_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightHamiltonianYinYangPair T.yinYangVacuumDomain = 0 := by
  ext <;> simp [yinYangVacuumDomain, rightHamiltonianYinYangPair]

/-- The algebraic Schrödinger vector field fixes the doubled vacuum. -/
@[simp] theorem rightSchrodingerVectorField_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightSchrodingerVectorField T.yinYangVacuumDomain = 0 := by
  rw [rightSchrodingerVectorField_apply]
  ext <;> simp [yinYangVacuumDomain]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
