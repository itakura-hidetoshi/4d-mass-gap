import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumIRMassLower
import Mathlib.Tactic

/-!
# Physical OS mass / infrared / log-decay / Rayleigh sandwich

The vacuum-sector transfer slope is now known to lie below the constructed
infrared physical OS logarithmic decay exponent.  Earlier layers already place
that infrared exponent below every positive finite-time normalized logarithmic
decay, and place the latter below the canonical right-Hamiltonian Rayleigh
quotient on the right-generator domain.

This file records the complete chain as a single public theorem:

`0 < mass ≤ m_IR(psi) ≤ normalizedLogDecay(psi,t) ≤ Rayleigh_H(psi)`.

It is purely a packaging layer: no spectral theorem, PVM, exponential-decay
hypothesis, self-adjointness assumption, or new physical axiom is introduced.
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

/-- Complete physical OS mass sandwich on a nonzero vacuum-orthogonal state in
the canonical right-generator domain. -/
theorem VacuumSemigroupGapSlope.mass_ir_normalizedLogDecay_rayleigh_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hpsi_ne : (psi : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    0 < G.mass ∧
      G.mass ≤
        T.physicalCorrelationRealClampInfraredEffectiveMass
          (psi : P.PhysicalHilbert) ∧
      T.physicalCorrelationRealClampInfraredEffectiveMass
          (psi : P.PhysicalHilbert) ≤
        T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          (psi : P.PhysicalHilbert) (t : ℝ) ∧
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          (psi : P.PhysicalHilbert) (t : ℝ) ≤
        ⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  constructor
  · exact G.mass_pos
  constructor
  · exact G.mass_le_infraredEffectiveMass
      T hSymmetric hpsi hpsi_ne
  · exact
      (T.physicalCorrelationRealClampNormalizedLogDecayFromZero_uv_ir_sandwich
        hSymmetric psi hpsi_ne t ht).2

/-- Finite-volume transfer wrapper for the complete physical OS mass sandwich. -/
theorem FiniteVolumeVacuumGapTransfer.mass_ir_normalizedLogDecay_rayleigh_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hpsi_ne : (psi : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    0 < G.mass ∧
      G.mass ≤
        T.physicalCorrelationRealClampInfraredEffectiveMass
          (psi : P.PhysicalHilbert) ∧
      T.physicalCorrelationRealClampInfraredEffectiveMass
          (psi : P.PhysicalHilbert) ≤
        T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          (psi : P.PhysicalHilbert) (t : ℝ) ∧
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          (psi : P.PhysicalHilbert) (t : ℝ) ≤
        ⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  constructor
  · exact G.mass_pos
  constructor
  · exact G.mass_le_infraredEffectiveMass
      T hSymmetric hpsi hpsi_ne
  · exact
      (T.physicalCorrelationRealClampNormalizedLogDecayFromZero_uv_ir_sandwich
        hSymmetric psi hpsi_ne t ht).2

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
