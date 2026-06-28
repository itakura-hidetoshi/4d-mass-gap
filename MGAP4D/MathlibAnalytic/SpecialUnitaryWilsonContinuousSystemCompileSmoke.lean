import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonContinuousSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def special_unitary_continuous_system_compile_smoke
    (L : CompactGaugeWilsonSystem)
    (N : ℕ)
    (gaugeEquiv :
      L.Gauge ≃ₜ* Matrix.specialUnitaryGroup (Fin N) ℂ)
    (plaquetteEnergy_eq :
      ∀ g : L.Gauge,
        L.plaquetteEnergy g =
          specialUnitaryWilsonPlaquetteEnergy N (gaugeEquiv g)) :
    ContinuousCompactGaugeWilsonSystem :=
  L.toContinuousOfSpecialUnitaryStandardEnergy
    N gaugeEquiv plaquetteEnergy_eq

end

end MathlibAnalytic
end MGAP4D
