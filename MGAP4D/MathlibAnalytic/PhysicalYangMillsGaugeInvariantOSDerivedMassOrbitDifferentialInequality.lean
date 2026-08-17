import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianOrbitNormDerivative
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSemigroupInvariant
import Mathlib.Tactic

/-!
# Derived physical mass controls the right derivative of excitation orbit norms

This layer connects the variational mass of the graph-closed physical Yang--Mills
Hamiltonian back to the canonical semigroup generator domain.

First, the closed-domain Rayleigh lower bound defining `physicalYangMillsMass`
is restricted along the canonical inclusion of the right Hamiltonian into its
graph closure.  Then vacuum-orthogonal invariance of the physical contraction
semigroup transports that lower bound to every positive-time orbit state.
Finally, the right-derivative theorem for the squared orbit norm turns the
quadratic lower bound into the differential inequality required for a later
Gronwall step.

No spectral theorem, functional-calculus identification `T_t = exp (-t H)`,
exact mass value, PVM atom, or new physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The variational mass of the graph-closed physical Hamiltonian already gives
the same quadratic lower bound on the canonical right-generator domain. -/
theorem physicalYangMillsMass_mul_norm_sq_le_rightHamiltonian_inner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalYangMillsMass *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  by_cases hpsi : (psi : P.PhysicalHilbert) = 0
  · simp [hpsi]
  · let psiClosed : T.closedRightHamiltonian.domain :=
      ⟨(psi : P.PhysicalHilbert),
        T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1 psi.property⟩
    have hclosed :=
      T.physicalYangMillsMass_mul_norm_sq_le_inner
        psiClosed
        (by simpa [psiClosed] using hpsi)
        (by simpa [psiClosed] using horthogonal)
    have hvalue :
        T.closedRightHamiltonian psiClosed =
          T.rightHamiltonian psi := by
      symm
      exact T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2 rfl
    simpa [psiClosed, hvalue] using hclosed

/-- The positive-time normalized slope of the squared orbit norm, based at an
arbitrary nonnegative time `s`. -/
def physicalOrbitNormSqShiftedSlope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s t : NNReal) : ℝ :=
  (t : ℝ)⁻¹ *
    (‖T.toPhysicalSemigroup.operator (s + t) psi‖ ^ 2 -
      ‖T.toPhysicalSemigroup.operator s psi‖ ^ 2)

/-- The shifted slope is exactly the zero-time slope of the already evolved
state. -/
theorem physicalOrbitNormSqShiftedSlope_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s t : NNReal) :
    T.physicalOrbitNormSqShiftedSlope psi s t =
      T.physicalOrbitNormSqSlope
        (T.toPhysicalSemigroup.operator s psi) t := by
  unfold physicalOrbitNormSqShiftedSlope physicalOrbitNormSqSlope
  have hadd :
      T.toPhysicalSemigroup.operator (s + t) psi =
        T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator s psi) := by
    calc
      T.toPhysicalSemigroup.operator (s + t) psi =
          T.toPhysicalSemigroup.operator (t + s) psi := by
        rw [add_comm]
      _ = T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator s psi) := by
        rw [T.toPhysicalSemigroup.operator_add]
        rfl
  rw [hadd]

/-- On the canonical generator domain, the shifted squared-norm slope converges
at every nonnegative base time to minus twice the right-Hamiltonian quadratic
form of the evolved state. -/
theorem physicalOrbitNormSqShiftedSlope_tendsto_rightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s : NNReal) (psi : T.rightGeneratorDomain) :
    Tendsto
      (fun t : NNReal =>
        T.physicalOrbitNormSqShiftedSlope
          (psi : P.PhysicalHilbert) s t)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (-2 * inner ℝ
          (T.rightHamiltonian
            ⟨T.toPhysicalSemigroup.operator s
                (psi : P.PhysicalHilbert),
              T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩)
          (T.toPhysicalSemigroup.operator s
            (psi : P.PhysicalHilbert)))) := by
  let psiS : T.rightGeneratorDomain :=
    ⟨T.toPhysicalSemigroup.operator s (psi : P.PhysicalHilbert),
      T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩
  have hbase :=
    T.physicalOrbitNormSqSlope_tendsto_rightHamiltonian psiS
  have hfun :
      (fun t : NNReal =>
        T.physicalOrbitNormSqShiftedSlope
          (psi : P.PhysicalHilbert) s t) =
        (fun t : NNReal =>
          T.physicalOrbitNormSqSlope
            (psiS : P.PhysicalHilbert) t) := by
    funext t
    simpa [psiS] using
      T.physicalOrbitNormSqShiftedSlope_eq
        (psi : P.PhysicalHilbert) s t
  rw [hfun]
  simpa [psiS] using hbase

/-- The derived physical Yang--Mills mass controls the right-Hamiltonian
quadratic form of every positive-time evolved vacuum-orthogonal generator-domain
state. -/
theorem physicalYangMillsMass_mul_norm_sq_le_rightHamiltonian_inner_operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (s : NNReal) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalYangMillsMass *
        ‖T.toPhysicalSemigroup.operator s
          (psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ
        (T.rightHamiltonian
          ⟨T.toPhysicalSemigroup.operator s
              (psi : P.PhysicalHilbert),
            T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩)
        (T.toPhysicalSemigroup.operator s
          (psi : P.PhysicalHilbert)) := by
  let psiS : T.rightGeneratorDomain :=
    ⟨T.toPhysicalSemigroup.operator s (psi : P.PhysicalHilbert),
      T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩
  have hmem0 :
      (psi : P.PhysicalHilbert) ∈ P.vacuumOrthogonal := by
    rw [P.mem_vacuumOrthogonal_iff, real_inner_comm]
    exact horthogonal
  have hmemS :
      T.toPhysicalSemigroup.operator s (psi : P.PhysicalHilbert) ∈
        P.vacuumOrthogonal :=
    T.toPhysicalSemigroup.operator_mem_vacuumOrthogonal_of_normalized
      hP s hmem0
  have horthS :
      inner ℝ (psiS : P.PhysicalHilbert) P.vacuum = 0 := by
    rw [real_inner_comm]
    have h :=
      (P.mem_vacuumOrthogonal_iff
        (T.toPhysicalSemigroup.operator s
          (psi : P.PhysicalHilbert))).mp hmemS
    simpa [psiS] using h
  simpa [psiS] using
    T.physicalYangMillsMass_mul_norm_sq_le_rightHamiltonian_inner
      psiS horthS

/-- The shifted right derivative therefore has the pointwise decay-rate upper
bound required for a Gronwall argument:

`D₊ ‖T_s psi‖² ≤ -2 * physicalYangMillsMass * ‖T_s psi‖²`.

The theorem records both the actual right-slope limit and the scalar inequality
satisfied by that limit. -/
theorem physicalOrbitNormSqShiftedSlope_tendsto_mass_decay_upper
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (s : NNReal) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Tendsto
      (fun t : NNReal =>
        T.physicalOrbitNormSqShiftedSlope
          (psi : P.PhysicalHilbert) s t)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (-2 * inner ℝ
          (T.rightHamiltonian
            ⟨T.toPhysicalSemigroup.operator s
                (psi : P.PhysicalHilbert),
              T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩)
          (T.toPhysicalSemigroup.operator s
            (psi : P.PhysicalHilbert)))) ∧
      (-2 * inner ℝ
          (T.rightHamiltonian
            ⟨T.toPhysicalSemigroup.operator s
                (psi : P.PhysicalHilbert),
              T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩)
          (T.toPhysicalSemigroup.operator s
            (psi : P.PhysicalHilbert)) ≤
        -2 * T.physicalYangMillsMass *
          ‖T.toPhysicalSemigroup.operator s
            (psi : P.PhysicalHilbert)‖ ^ 2) := by
  refine ⟨T.physicalOrbitNormSqShiftedSlope_tendsto_rightHamiltonian s psi, ?_⟩
  have hmass :=
    T.physicalYangMillsMass_mul_norm_sq_le_rightHamiltonian_inner_operator
      hP s psi horthogonal
  nlinarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
