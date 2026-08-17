import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationInfraredEffectiveMass
import Mathlib.Tactic

/-!
# Infrared effective mass as normalized physical OS log decay

The zero-based unregularized effective mass is definitionally the normalized
loss of the logarithmic physical OS correlation,

`(log C̃_psi(0) - log C̃_psi(t)) / t`.

The preceding infrared theorem constructed the long-time limit of the same
quantity from convexity and monotone convergence.  This file records that
identification explicitly, so the next spectral step can consume a genuine
long-time logarithmic decay exponent rather than an abstract effective-mass
name.

For every nonzero right-generator-domain state we also retain the complete
finite-time sandwich between the constructed infrared exponent and the
right-Hamiltonian Rayleigh quotient.

No spectral theorem, PVM, self-adjointness assumption, exponential decay
hypothesis, or new physical axiom is introduced.
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

/-- Normalized logarithmic decay of the physical OS correlation from Euclidean
time zero.  For positive `t` this is exactly the zero-based unregularized
effective mass. -/
def physicalCorrelationRealClampNormalizedLogDecayFromZero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : ℝ) : ℝ :=
  (T.physicalCorrelationRealClampLog psi 0 -
      T.physicalCorrelationRealClampLog psi t) / t

/-- At every positive Euclidean time, normalized logarithmic decay from zero is
exactly the zero-based unregularized effective mass. -/
theorem physicalCorrelationRealClampNormalizedLogDecayFromZero_eq_effectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert)
    {t : ℝ} :
    T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi t =
      T.physicalCorrelationRealClampEffectiveMass psi 0 t := by
  unfold physicalCorrelationRealClampNormalizedLogDecayFromZero
  unfold physicalCorrelationRealClampEffectiveMass
  unfold MGAP4D.secantDecayRate
  ring

/-- The normalized physical OS logarithmic decay along the continuous cofinal
tail `t = u + 1` converges to the constructed infrared effective mass. -/
theorem physicalCorrelationRealClampNormalizedLogDecayFromZero_shift_tendsto_infrared
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    Tendsto
      (fun u : NNReal =>
        T.physicalCorrelationRealClampNormalizedLogDecayFromZero
          psi (((u + 1 : NNReal) : ℝ)))
      atTop
      (nhds (T.physicalCorrelationRealClampInfraredEffectiveMass psi)) := by
  simpa only [
    T.physicalCorrelationRealClampNormalizedLogDecayFromZero_eq_effectiveMass
  ] using
    T.physicalCorrelationRealClampEffectiveMass_shift_tendsto_infrared
      hSymmetric hpsi

/-- The constructed infrared exponent is below every positive finite-time
normalized logarithmic decay from zero. -/
theorem physicalCorrelationRealClampInfraredEffectiveMass_le_normalizedLogDecayFromZero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    T.physicalCorrelationRealClampInfraredEffectiveMass psi ≤
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero
        psi (t : ℝ) := by
  rw [T.physicalCorrelationRealClampNormalizedLogDecayFromZero_eq_effectiveMass]
  exact
    T.physicalCorrelationRealClampInfraredEffectiveMass_le_effectiveMass_zero
      hSymmetric hpsi t ht

/-- UV-to-IR sandwich written directly in terms of the normalized logarithmic
physical OS decay. -/
theorem physicalCorrelationRealClampNormalizedLogDecayFromZero_uv_ir_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    0 ≤ T.physicalCorrelationRealClampInfraredEffectiveMass
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
  simpa only [
    T.physicalCorrelationRealClampNormalizedLogDecayFromZero_eq_effectiveMass
  ] using
    T.physicalCorrelationRealClampEffectiveMass_uv_ir_sandwich
      hSymmetric psi hpsi t ht

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
