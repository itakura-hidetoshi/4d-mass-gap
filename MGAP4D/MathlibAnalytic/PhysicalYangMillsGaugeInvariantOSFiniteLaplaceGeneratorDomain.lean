import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteLaplacePrimitiveDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Applying completed Euclidean-time evolution to a weighted orbit shifts its
real-time argument and produces the compensating exponential factor. -/
theorem physicalOperator_exponentiallyWeightedPhysicalOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (t : NNReal) (psi : P.PhysicalHilbert)
    (s : ℝ) (hs : 0 ≤ s) :
    T.toPhysicalSemigroup.operator t
        (T.exponentiallyWeightedPhysicalOrbit lambda psi s) =
      Real.exp (lambda * (t : ℝ)) •
        T.exponentiallyWeightedPhysicalOrbit lambda psi
          (s + (t : ℝ)) := by
  calc
    T.toPhysicalSemigroup.operator t
        (T.exponentiallyWeightedPhysicalOrbit lambda psi s) =
      Real.exp ((-lambda) * s) •
        T.toPhysicalSemigroup.operator t (T.realPhysicalOrbit psi s) := by
          simp [exponentiallyWeightedPhysicalOrbit, map_smul]
    _ = Real.exp ((-lambda) * s) •
        T.realPhysicalOrbit
          (T.toPhysicalSemigroup.operator t psi) s := by
          rw [T.physicalOperator_realPhysicalOrbit]
    _ = Real.exp ((-lambda) * s) •
        T.realPhysicalOrbit psi (s + (t : ℝ)) := by
          rw [T.realPhysicalOrbit_operator_eq_add_of_nonneg t psi s hs]
    _ = Real.exp (lambda * (t : ℝ)) •
        T.exponentiallyWeightedPhysicalOrbit lambda psi
          (s + (t : ℝ)) := by
          rw [exponentiallyWeightedPhysicalOrbit, smul_smul]
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring

/-- Applying the semigroup to a finite Laplace integral gives the shifted
exponential primitive. -/
theorem physicalOperator_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (t h : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator t
        (T.finiteLaplaceIntegral lambda h psi) =
      T.shiftedExponentialTimePrimitive lambda h psi (t : ℝ) := by
  unfold finiteLaplaceIntegral exponentialTimePrimitive
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (T.toPhysicalSemigroup.operator t)
    (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
      lambda psi 0 (h : ℝ))]
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
        T.toPhysicalSemigroup.operator t
          (T.exponentiallyWeightedPhysicalOrbit lambda psi s)) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        Real.exp (lambda * (t : ℝ)) •
          T.exponentiallyWeightedPhysicalOrbit lambda psi
            (s + (t : ℝ)) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hh : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
          rw [uIcc_of_le hh] at hs
          exact T.physicalOperator_exponentiallyWeightedPhysicalOrbit
            lambda t psi s hs.1
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (0 : ℝ)..(h : ℝ),
          T.exponentiallyWeightedPhysicalOrbit lambda psi
            (s + (t : ℝ))) := by
          rw [intervalIntegral.integral_smul]
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
          T.exponentiallyWeightedPhysicalOrbit lambda psi s) := by
          rw [intervalIntegral.integral_comp_add_right]
          simp
    _ = T.shiftedExponentialTimePrimitive lambda h psi (t : ℝ) := by
          unfold shiftedExponentialTimePrimitive exponentialTimePrimitive
          congr 1
          symm
          simpa [add_comm] using
            intervalIntegral.integral_interval_sub_left
              (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
                lambda psi 0 ((t : ℝ) + (h : ℝ)))
              (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
                lambda psi 0 (t : ℝ))

/-- The right difference quotient of a finite Laplace integral is the slope of
its shifted exponential primitive. -/
theorem rightDifferenceQuotient_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h t : NNReal) (psi : P.PhysicalHilbert) :
    T.rightDifferenceQuotient
        (T.finiteLaplaceIntegral lambda h psi) t =
      (t : ℝ)⁻¹ •
        (T.shiftedExponentialTimePrimitive lambda h psi (t : ℝ) -
          T.shiftedExponentialTimePrimitive lambda h psi 0) := by
  unfold rightDifferenceQuotient
  rw [T.physicalOperator_finiteLaplaceIntegral]
  rw [T.shiftedExponentialTimePrimitive_zero]

/-- Every finite Laplace integral has the expected right-generator value. -/
theorem hasRightGeneratorValue_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.HasRightGeneratorValue
      (T.finiteLaplaceIntegral lambda h psi)
      (lambda • T.finiteLaplaceIntegral lambda h psi +
        Real.exp ((-lambda) * (h : ℝ)) •
          T.toPhysicalSemigroup.operator h psi - psi) := by
  unfold HasRightGeneratorValue
  have hreal :=
    (T.shiftedExponentialTimePrimitive_hasDerivAt_zero_explicit
      lambda h psi).tendsto_slope_zero_right
  have hcomp := hreal.comp nnreal_coe_tendsto_zero_right
  simpa only [T.rightDifferenceQuotient_finiteLaplaceIntegral,
    zero_add] using hcomp

/-- Every finite Laplace integral belongs to the canonical right-generator
and right-Hamiltonian domain. -/
theorem finiteLaplaceIntegral_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.finiteLaplaceIntegral lambda h psi ∈ T.rightGeneratorDomain :=
  ⟨lambda • T.finiteLaplaceIntegral lambda h psi +
      Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi - psi,
    T.hasRightGeneratorValue_finiteLaplaceIntegral lambda h psi⟩

/-- The finite Laplace integral bundled in the canonical generator domain. -/
def finiteLaplaceIntegralGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGeneratorDomain :=
  ⟨T.finiteLaplaceIntegral lambda h psi,
    T.finiteLaplaceIntegral_mem_rightGeneratorDomain lambda h psi⟩

@[simp] theorem finiteLaplaceIntegralGeneratorDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.finiteLaplaceIntegralGeneratorDomain lambda h psi :
      P.PhysicalHilbert) = T.finiteLaplaceIntegral lambda h psi :=
  rfl

/-- The canonical generator evaluates on a finite Laplace integral by the
finite-time resolvent formula. -/
theorem rightGenerator_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGenerator
        (T.finiteLaplaceIntegralGeneratorDomain lambda h psi) =
      lambda • T.finiteLaplaceIntegral lambda h psi +
        Real.exp ((-lambda) * (h : ℝ)) •
          T.toPhysicalSemigroup.operator h psi - psi := by
  apply T.hasRightGeneratorValue_unique
    (T.rightGenerator_hasRightGeneratorValue
      (T.finiteLaplaceIntegralGeneratorDomain lambda h psi))
  exact T.hasRightGeneratorValue_finiteLaplaceIntegral lambda h psi

/-- The positive shift `lambda I + H` on the canonical right-Hamiltonian
domain. -/
noncomputable def rightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup) (lambda : ℝ) :
    T.rightGeneratorDomain →ₗ[ℝ] P.PhysicalHilbert :=
  lambda • T.rightGeneratorDomain.subtype + T.rightHamiltonian

@[simp] theorem rightHamiltonianShift_apply
    (T : P.StronglyContinuousPhysicalSemigroup) (lambda : ℝ)
    (psi : T.rightGeneratorDomain) :
    T.rightHamiltonianShift lambda psi =
      lambda • (psi : P.PhysicalHilbert) + T.rightHamiltonian psi :=
  rfl

/-- The positive canonical Hamiltonian shift maps a finite Laplace integral to
`psi` minus its exponentially decaying terminal orbit. -/
theorem rightHamiltonianShift_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightHamiltonianShift lambda
        (T.finiteLaplaceIntegralGeneratorDomain lambda h psi) =
      psi - Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi := by
  rw [T.rightHamiltonianShift_apply, T.rightHamiltonian_apply,
    T.rightGenerator_finiteLaplaceIntegral]
  module

/-- The same finite Laplace vector, now bundled in the domain of the closed
right Hamiltonian. -/
def finiteLaplaceIntegralClosedDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian.domain :=
  ⟨T.finiteLaplaceIntegral lambda h psi,
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
      (T.finiteLaplaceIntegral_mem_rightGeneratorDomain lambda h psi)⟩

@[simp] theorem finiteLaplaceIntegralClosedDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.finiteLaplaceIntegralClosedDomain lambda h psi :
      P.PhysicalHilbert) = T.finiteLaplaceIntegral lambda h psi :=
  rfl

/-- The closed Hamiltonian agrees with the canonical Hamiltonian on finite
Laplace integrals. -/
theorem closedRightHamiltonian_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian
        (T.finiteLaplaceIntegralClosedDomain lambda h psi) =
      T.rightHamiltonian
        (T.finiteLaplaceIntegralGeneratorDomain lambda h psi) := by
  exact T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2
    (x := T.finiteLaplaceIntegralGeneratorDomain lambda h psi)
    (y := T.finiteLaplaceIntegralClosedDomain lambda h psi) rfl

/-- The positive shift of the closed right Hamiltonian obeys the finite-time
Laplace resolvent identity. -/
theorem closedRightHamiltonianShift_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonianShift lambda
        (T.finiteLaplaceIntegralClosedDomain lambda h psi) =
      psi - Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi := by
  simpa only [T.closedRightHamiltonianShift_apply,
    T.closedRightHamiltonian_finiteLaplaceIntegral,
    T.rightHamiltonianShift_apply] using
      T.rightHamiltonianShift_finiteLaplaceIntegral lambda h psi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
