import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def special_unitary_compact_wilson_system_compile_smoke
    (geometry : FiniteFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactGaugeWilsonSystem :=
  specialUnitaryContinuousCompactGaugeWilsonSystem
    geometry N hN beta beta_nonneg

end

end MathlibAnalytic
end MGAP4D
