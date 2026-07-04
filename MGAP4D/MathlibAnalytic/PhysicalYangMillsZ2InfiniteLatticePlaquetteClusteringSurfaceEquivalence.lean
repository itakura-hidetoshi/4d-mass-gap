import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringConstructionAPI
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- The existential weak-limit/observable surface yields the construction-level
API surface. -/
theorem existsConstruction_of_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette →
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette := by
  intro h
  exact
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_of_nonempty
      beta hBeta distance sourcePlaquette targetPlaquette
      (nonempty_of_existsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette h)

/-- The construction-level API surface yields the existential weak-limit and
observable surface. -/
theorem existsLimitObservables_of_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette →
      ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette := by
  intro h
  exact
    existsLimitObservables_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringNonempty_of_existsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette h)

/-- The existential weak-limit/observable surface is equivalent to the
construction-level API surface. -/
theorem existsLimitObservables_iff_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette ↔
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · exact
      existsConstruction_of_existsLimitObservables beta hBeta distance sourcePlaquette
        targetPlaquette
  · exact
      existsLimitObservables_of_existsConstruction beta hBeta distance sourcePlaquette
        targetPlaquette

/-- Explicit façade data produce the construction-level API surface via the
existential weak-limit/observable surface.

This theorem is only a surface-conversion layer for the compact infinite-lattice
binary carrier.  It keeps the supplied all-volume plaquette distance hypothesis
and finite-volume clustering certificate as hypotheses and does not assert a
Hamiltonian spectral gap or a physical mass gap. -/
theorem existsConstruction_ofData_via_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
      beta hBeta distance sourcePlaquette targetPlaquette :=
  (existsLimitObservables_iff_existsConstruction beta hBeta distance sourcePlaquette
    targetPlaquette).mp
      (existsLimitObservables_ofData beta hBeta distance sourcePlaquette targetPlaquette
        hDistance K)

/-- Explicit façade data produce the existential weak-limit/observable surface
via the construction-level API surface. -/
theorem existsLimitObservables_ofData_via_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette :=
  (existsLimitObservables_iff_existsConstruction beta hBeta distance sourcePlaquette
    targetPlaquette).mpr
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_ofData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
