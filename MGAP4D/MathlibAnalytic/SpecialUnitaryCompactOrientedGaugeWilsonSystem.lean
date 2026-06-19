import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical compact `SU(N)` Wilson system on a finite signed plaquette
geometry. -/
def specialUnitaryCompactOrientedGaugeWilsonSystem
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    CompactOrientedGaugeWilsonSystem := by
  letI : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupCompactSpace N
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupSecondCountableTopology N
  letI : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupMeasurableSpace N
  letI : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupBorelSpace N
  exact
    { Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
      geometry := geometry
      plaquetteEnergy := specialUnitaryWilsonPlaquetteEnergy N
      plaquetteEnergy_nonneg := specialUnitaryWilsonPlaquetteEnergy_nonneg hN
      plaquetteEnergy_conjInvariant :=
        specialUnitaryWilsonPlaquetteEnergy_conjInvariant
      beta := beta
      beta_nonneg := beta_nonneg }

/-- Continuous canonical `SU(N)` Wilson system on signed physical-link
geometry. -/
def specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem := by
  letI : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupCompactSpace N
  letI : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupSecondCountableTopology N
  letI : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupMeasurableSpace N
  letI : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    specialUnitaryGroupBorelSpace N
  exact
    { base := specialUnitaryCompactOrientedGaugeWilsonSystem
        geometry N hN beta beta_nonneg
      plaquetteEnergy_continuous := by
        simpa only [specialUnitaryCompactOrientedGaugeWilsonSystem] using
          continuous_specialUnitaryWilsonPlaquetteEnergy N }

end

end MathlibAnalytic
end MGAP4D
