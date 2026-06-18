import MGAP4D.MathlibAnalytic.FiniteFourDimensionalPlaquetteGeometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite compact-gauge Wilson system associated with finite four-step
plaquette geometry and the canonical `SU(N)` Wilson energy.  The canonical
finite-dimensional topology, compactness, second-countability, measurable, and
Borel receipts are constructed internally. -/
def specialUnitaryCompactGaugeWilsonSystem
    (geometry : FiniteFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    CompactGaugeWilsonSystem := by
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
      Vertex := geometry.Vertex
      Edge := geometry.Edge
      Plaquette := geometry.Plaquette
      source := geometry.source
      target := geometry.target
      boundary := geometry.boundary
      boundary_cycle_01 := geometry.boundary_cycle_01
      boundary_cycle_12 := geometry.boundary_cycle_12
      boundary_cycle_23 := geometry.boundary_cycle_23
      boundary_cycle_30 := geometry.boundary_cycle_30
      plaquetteEnergy := specialUnitaryWilsonPlaquetteEnergy N
      plaquetteEnergy_nonneg := specialUnitaryWilsonPlaquetteEnergy_nonneg hN
      plaquetteEnergy_conjInvariant :=
        specialUnitaryWilsonPlaquetteEnergy_conjInvariant
      beta := beta
      beta_nonneg := beta_nonneg }

/-- The canonical finite `SU(N)` Wilson system with continuous plaquette energy.
All standard topology and Borel receipts are discharged internally. -/
def specialUnitaryContinuousCompactGaugeWilsonSystem
    (geometry : FiniteFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactGaugeWilsonSystem := by
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
    { base := specialUnitaryCompactGaugeWilsonSystem
        geometry N hN beta beta_nonneg
      plaquetteEnergy_continuous := by
        simpa only [specialUnitaryCompactGaugeWilsonSystem] using
          continuous_specialUnitaryWilsonPlaquetteEnergy N }

end

end MathlibAnalytic
end MGAP4D
