import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryStandardEnergy
import Mathlib.Topology.Algebra.ContinuousMonoidHom

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A compact-gauge Wilson system whose gauge group is topologically identified
with `SU(N)` and whose energy is the canonical Wilson energy is automatically a
continuous compact-gauge Wilson system. -/
def CompactGaugeWilsonSystem.toContinuousOfSpecialUnitaryStandardEnergy
    (L : CompactGaugeWilsonSystem)
    (N : ℕ)
    (gaugeEquiv :
      L.Gauge ≃ₜ* Matrix.specialUnitaryGroup (Fin N) ℂ)
    (plaquetteEnergy_eq :
      ∀ g : L.Gauge,
        L.plaquetteEnergy g =
          specialUnitaryWilsonPlaquetteEnergy N (gaugeEquiv g)) :
    ContinuousCompactGaugeWilsonSystem :=
  { base := L
    plaquetteEnergy_continuous := by
      rw [show L.plaquetteEnergy =
          fun g => specialUnitaryWilsonPlaquetteEnergy N (gaugeEquiv g) by
        funext g
        exact plaquetteEnergy_eq g]
      exact
        (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp
          gaugeEquiv.continuous_toFun }

end

end MathlibAnalytic
end MGAP4D
