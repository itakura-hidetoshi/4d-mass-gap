import MGAP4D.MathlibAnalytic.FiniteFourDimensionalPlaquetteGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite compact-gauge Wilson system associated with finite four-step
plaquette geometry and the canonical `SU(N)` Wilson energy. -/
def specialUnitaryCompactGaugeWilsonSystem
    (geometry : FiniteFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    CompactGaugeWilsonSystem :=
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

/-- The canonical finite `SU(N)` Wilson system is automatically continuous. -/
def specialUnitaryContinuousCompactGaugeWilsonSystem
    (geometry : FiniteFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactGaugeWilsonSystem :=
  { base := specialUnitaryCompactGaugeWilsonSystem
      geometry N hN beta beta_nonneg
    plaquetteEnergy_continuous :=
      continuous_specialUnitaryWilsonPlaquetteEnergy N }

end

end MathlibAnalytic
end MGAP4D
