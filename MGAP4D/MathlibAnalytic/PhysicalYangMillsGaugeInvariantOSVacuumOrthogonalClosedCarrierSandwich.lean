import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSMassInfraredLogDecayRayleighSandwich
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
import Mathlib.Tactic

/-!
# Vacuum-orthogonal closed-carrier OS mass bounds

The physical OS mass / infrared / finite-time logarithmic-decay chain and the
closed right-Hamiltonian coercive estimate are already available separately.
This file packages them on the canonical vacuum-orthogonal closed-Hamiltonian
carrier.

For a nonzero state in `vacuumOrthogonalClosedRightHamiltonianDomain` and every
positive Euclidean time `t`, the result records

`0 < mass ≤ m_IR(psi) ≤ normalizedLogDecay(psi,t)`

simultaneously with the closed quadratic-form estimate

`mass * ‖psi‖^2 ≤ ⟪closedRightHamiltonian psi, psi⟫`.

This is deliberately not an assertion that the finite-time logarithmic decay is
bounded above by a closed-domain Rayleigh quotient; the existing such upper
bound remains on the right-generator domain.  No new analytic hypothesis,
spectral theorem, PVM, or physical axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- On the vacuum-orthogonal closed-Hamiltonian carrier, the transfer mass is a
strictly positive lower bound for the infrared physical OS exponent, which is
below every positive finite-time normalized logarithmic decay; at the same time
the same mass is the closed right-Hamiltonian quadratic-form coercivity
constant. -/
theorem VacuumSemigroupGapSlope.mass_ir_normalizedLogDecay_closedCarrier_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hP : P.IsNormalized)
    (x : T.vacuumOrthogonalClosedRightHamiltonianDomain)
    (hx_ne :
      (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    0 < G.mass ∧
      G.mass ≤
        T.physicalCorrelationRealClampInfraredEffectiveMass
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) ∧
      T.physicalCorrelationRealClampInfraredEffectiveMass
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) ≤
        T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert)
          (t : ℝ) ∧
      G.mass *
          ‖(T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert)‖ ^ 2 ≤
        inner ℝ
          (T.closedRightHamiltonian
            (T.vacuumOrthogonalAmbientDomainPoint x))
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) := by
  have hx_left :
      inner ℝ P.vacuum
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) = 0 := by
    change inner ℝ P.vacuum
      ((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) = 0
    exact
      (P.mem_vacuumOrthogonal_iff
        ((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)).mp
        (x : P.VacuumOrthogonalHilbert).property
  have hx_orth :
      inner ℝ
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert)
          P.vacuum = 0 := by
    rw [real_inner_comm]
    exact hx_left
  constructor
  · exact G.mass_pos
  constructor
  · exact G.mass_le_infraredEffectiveMass
      T hSymmetric hx_orth hx_ne
  constructor
  · exact
      T.physicalCorrelationRealClampInfraredEffectiveMass_le_normalizedLogDecayFromZero
        hSymmetric hx_ne t ht
  · exact
      G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
        T hP (T.vacuumOrthogonalAmbientDomainPoint x) hx_orth

/-- Finite-volume transfer wrapper for the vacuum-orthogonal closed-carrier
mass / infrared / logarithmic-decay and closed coercivity package. -/
theorem FiniteVolumeVacuumGapTransfer.mass_ir_normalizedLogDecay_closedCarrier_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hP : P.IsNormalized)
    (x : T.vacuumOrthogonalClosedRightHamiltonianDomain)
    (hx_ne :
      (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    0 < G.mass ∧
      G.mass ≤
        T.physicalCorrelationRealClampInfraredEffectiveMass
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) ∧
      T.physicalCorrelationRealClampInfraredEffectiveMass
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) ≤
        T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert)
          (t : ℝ) ∧
      G.mass *
          ‖(T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert)‖ ^ 2 ≤
        inner ℝ
          (T.closedRightHamiltonian
            (T.vacuumOrthogonalAmbientDomainPoint x))
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) := by
  have hx_left :
      inner ℝ P.vacuum
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert) = 0 := by
    change inner ℝ P.vacuum
      ((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) = 0
    exact
      (P.mem_vacuumOrthogonal_iff
        ((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)).mp
        (x : P.VacuumOrthogonalHilbert).property
  have hx_orth :
      inner ℝ
          (T.vacuumOrthogonalAmbientDomainPoint x : P.PhysicalHilbert)
          P.vacuum = 0 := by
    rw [real_inner_comm]
    exact hx_left
  constructor
  · exact G.mass_pos
  constructor
  · exact G.mass_le_infraredEffectiveMass
      T hSymmetric hx_orth hx_ne
  constructor
  · exact
      T.physicalCorrelationRealClampInfraredEffectiveMass_le_normalizedLogDecayFromZero
        hSymmetric hx_ne t ht
  · exact
      G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
        T hP (T.vacuumOrthogonalAmbientDomainPoint x) hx_orth

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
