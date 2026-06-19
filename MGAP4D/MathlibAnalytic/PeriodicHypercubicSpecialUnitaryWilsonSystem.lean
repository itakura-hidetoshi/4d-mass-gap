import MGAP4D.MathlibAnalytic.PeriodicHypercubicFiniteOrientedGeometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical finite-volume `SU(N)` Wilson system on the signed periodic
four-dimensional lattice. -/
def periodicHypercubicSpecialUnitaryWilsonSystem
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
    (periodicHypercubicFiniteOrientedGeometry n)
    N hN beta beta_nonneg

end

end MathlibAnalytic
end MGAP4D
