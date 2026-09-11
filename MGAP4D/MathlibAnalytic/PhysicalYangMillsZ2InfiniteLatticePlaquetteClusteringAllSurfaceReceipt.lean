import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringCombinedSurfaceProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- A receipt form of the combined compact infinite-lattice `Z₂` plaquette-
clustering API surface.

The receipt stores the nonempty construction package surface, the weak-limit and
observable existential surface, the construction-level API surface, and the
expanded package-with-bound surface.  It is only a structured packaging of the
already formalized compact binary-carrier API. -/
structure AllSurfaceReceipt
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) where
  nonempty :
    Nonempty
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
        beta hBeta distance sourcePlaquette targetPlaquette)
  existsLimitObservables :
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette
  existsConstruction :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
      beta hBeta distance sourcePlaquette targetPlaquette
  existsPackageConnectedCorrelation_abs_le :
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
                  (distance : ℝ))

namespace AllSurfaceReceipt

/-- Build a receipt from the combined API surface. -/
noncomputable def ofAllSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (h : AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette) :
    AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette :=
  { nonempty :=
      allSurfaces_nonempty beta hBeta distance sourcePlaquette targetPlaquette h
    existsLimitObservables :=
      allSurfaces_existsLimitObservables beta hBeta distance sourcePlaquette
        targetPlaquette h
    existsConstruction :=
      allSurfaces_existsConstruction beta hBeta distance sourcePlaquette
        targetPlaquette h
    existsPackageConnectedCorrelation_abs_le :=
      allSurfaces_exists_package_connectedCorrelation_abs_le beta hBeta distance
        sourcePlaquette targetPlaquette h }

/-- A receipt yields the combined API surface. -/
theorem allSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette →
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette := by
  intro R
  exact ⟨R.nonempty, R.existsLimitObservables, R.existsConstruction⟩

/-- Receipts are equivalent to the combined API surface. -/
theorem nonempty_receipt_iff_allSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) ↔
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · rintro ⟨R⟩
    exact allSurfaces beta hBeta distance sourcePlaquette targetPlaquette R
  · intro h
    exact ⟨ofAllSurfaces beta hBeta distance sourcePlaquette targetPlaquette h⟩

/-- Explicit façade data produce a receipt for the combined compact
infinite-lattice `Z₂` plaquette-clustering surface.

This receipt is still a compact-carrier API object.  It keeps the all-volume
plaquette distance hypothesis and finite-volume clustering certificate as
hypotheses and does not assert a continuum construction, Hamiltonian spectral
gap, physical mass gap, or an unconditional proof of the four-dimensional
Yang--Mills mass gap problem. -/
noncomputable def ofData
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
    AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette :=
  ofAllSurfaces beta hBeta distance sourcePlaquette targetPlaquette
    (allSurfaces_ofData beta hBeta distance sourcePlaquette targetPlaquette
      hDistance K)

/-- Explicit façade data give a nonempty receipt. -/
theorem nonempty_ofData
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
    Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) :=
  ⟨ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K⟩

/-- The explicit façade-data receipt projects to the nonempty construction
surface. -/
theorem ofData_nonempty
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
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).nonempty =
      allSurfaces_ofData_nonempty beta hBeta distance sourcePlaquette
        targetPlaquette hDistance K :=
  rfl

/-- The explicit façade-data receipt projects to the weak-limit/observable
surface. -/
theorem ofData_existsLimitObservables
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
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).existsLimitObservables =
      allSurfaces_ofData_existsLimitObservables beta hBeta distance sourcePlaquette
        targetPlaquette hDistance K :=
  rfl

/-- The explicit façade-data receipt projects to the construction API surface. -/
theorem ofData_existsConstruction
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
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).existsConstruction =
      allSurfaces_ofData_existsConstruction beta hBeta distance sourcePlaquette
        targetPlaquette hDistance K :=
  rfl

/-- The explicit façade-data receipt projects to the expanded package-with-bound
surface. -/
theorem ofData_existsPackageConnectedCorrelation_abs_le
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
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).existsPackageConnectedCorrelation_abs_le =
      allSurfaces_ofData_exists_package_connectedCorrelation_abs_le beta hBeta distance
        sourcePlaquette targetPlaquette hDistance K :=
  rfl

end AllSurfaceReceipt

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
