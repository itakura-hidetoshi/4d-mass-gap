import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringPublicResult
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
namespace PublicPlaquetteClusteringResult

/-- A public result package gives the exponential connected-correlation bound
with the explicit source and target infinite-lattice plaquette observables as the
arguments of the selected weak-limit correlation.

This removes the last API indirection through the fields
`construction.sourceObservable` and `construction.targetObservable`. -/
theorem plaquetteObservable_connectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (R : PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette) :
    abs (R.construction.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable sourcePlaquette)
        (z2InfiniteHypercubicPlaquetteObservable targetPlaquette)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [R.sourceObservable_eq, R.targetObservable_eq]
    using R.connectedCorrelation_abs_le

/-- Explicit façade data give the public plaquette-observable connected-
correlation bound for the selected Prokhorov weak-limit construction package. -/
theorem ofData_plaquetteObservable_connectedCorrelation_abs_le
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
    abs ((ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).construction.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable sourcePlaquette)
        (z2InfiniteHypercubicPlaquetteObservable targetPlaquette)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  plaquetteObservable_connectedCorrelation_abs_le beta hBeta distance
    sourcePlaquette targetPlaquette
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Final public theorem from explicit compact-carrier façade data to an
existential selected weak limit whose connected correlation between the explicit
source and target infinite-lattice plaquette observables satisfies the
exponential clustering bound.

The statement stays inside the compact infinite-lattice binary carrier.  It
keeps the all-volume plaquette distance hypothesis and the finite-volume
clustering certificate as hypotheses, and it does not assert a continuum
Yang--Mills construction, Hamiltonian spectral gap, physical mass gap, or an
unconditional proof of the four-dimensional Yang--Mills mass gap problem. -/
theorem exists_public_result_plaquetteObservable_connectedCorrelation_abs_le_ofData
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
    ∃ (R : PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette),
      abs (R.construction.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
          (z2InfiniteHypercubicPlaquetteObservable sourcePlaquette)
          (z2InfiniteHypercubicPlaquetteObservable targetPlaquette)) ≤
        z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
          Real.exp
            (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
              (distance : ℝ)) := by
  refine
    ⟨ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K, ?_⟩
  exact
    ofData_plaquetteObservable_connectedCorrelation_abs_le beta hBeta distance
      sourcePlaquette targetPlaquette hDistance K

end PublicPlaquetteClusteringResult
end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
