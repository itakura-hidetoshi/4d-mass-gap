import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringCombinedSurface
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- Project nonempty construction packages from the combined API surface. -/
theorem allSurfaces_nonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette →
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) := by
  intro h
  exact h.1

/-- Project the weak-limit/observable existential surface from the combined API
surface. -/
theorem allSurfaces_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette →
      ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette := by
  intro h
  exact h.2.1

/-- Project the construction-level API surface from the combined API surface. -/
theorem allSurfaces_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette →
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette := by
  intro h
  exact h.2.2

/-- The combined API surface gives an explicit construction package with the two
plaquette observable identities and the exponential connected-correlation bound. -/
theorem allSurfaces_exists_package_connectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette →
      ∃ (C :
          z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
            beta hBeta distance sourcePlaquette targetPlaquette),
        C.sourceObservable = z2InfiniteHypercubicPlaquetteObservable sourcePlaquette ∧
          C.targetObservable = z2InfiniteHypercubicPlaquetteObservable targetPlaquette ∧
            abs (C.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
                C.sourceObservable C.targetObservable) ≤
              z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
                Real.exp
                  (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
                    (distance : ℝ)) := by
  intro h
  exact h.2.2

/-- Explicit façade data give the combined surface and then the nonempty
construction package projection. -/
theorem allSurfaces_ofData_nonempty
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
    Nonempty
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
        beta hBeta distance sourcePlaquette targetPlaquette) :=
  allSurfaces_nonempty beta hBeta distance sourcePlaquette targetPlaquette
    (allSurfaces_ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data give the combined surface and then the weak-limit
observable existential projection. -/
theorem allSurfaces_ofData_existsLimitObservables
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
  allSurfaces_existsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette
    (allSurfaces_ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data give the combined surface and then the construction API
projection. -/
theorem allSurfaces_ofData_existsConstruction
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
  allSurfaces_existsConstruction beta hBeta distance sourcePlaquette targetPlaquette
    (allSurfaces_ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data give the combined surface and then an explicit package
with the source and target observable identities and the exponential
connected-correlation bound.

This theorem is still only a projection API for the compact infinite-lattice
binary carrier.  It preserves the all-volume plaquette distance hypothesis and
finite-volume clustering certificate as hypotheses and does not assert a
continuum construction, Hamiltonian spectral gap, physical mass gap, or an
unconditional proof of the four-dimensional Yang--Mills mass gap problem. -/
theorem allSurfaces_ofData_exists_package_connectedCorrelation_abs_le
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
    ∃ (C :
        z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette),
      C.sourceObservable = z2InfiniteHypercubicPlaquetteObservable sourcePlaquette ∧
        C.targetObservable = z2InfiniteHypercubicPlaquetteObservable targetPlaquette ∧
          abs (C.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
              C.sourceObservable C.targetObservable) ≤
            z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
              Real.exp
                (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
                  (distance : ℝ)) :=
  allSurfaces_exists_package_connectedCorrelation_abs_le beta hBeta distance
    sourcePlaquette targetPlaquette
    (allSurfaces_ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
