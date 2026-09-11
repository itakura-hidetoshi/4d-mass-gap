import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringAllSurfaceReceipt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
namespace AllSurfaceReceipt

/-- Nonempty receipts are equivalent to nonempty construction packages. -/
theorem nonempty_receipt_iff_nonemptyConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) ↔
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) := by
  constructor
  · intro hReceipt
    exact
      allSurfaces_nonempty beta hBeta distance sourcePlaquette targetPlaquette
        ((nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
          targetPlaquette).mp hReceipt)
  · intro hNonempty
    exact
      (nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
        targetPlaquette).mpr
        (allSurfaces_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
          hNonempty)

/-- Nonempty receipts are equivalent to the weak-limit/observable existential
surface. -/
theorem nonempty_receipt_iff_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) ↔
      ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · intro hReceipt
    exact
      allSurfaces_existsLimitObservables beta hBeta distance sourcePlaquette
        targetPlaquette
        ((nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
          targetPlaquette).mp hReceipt)
  · intro hExists
    exact
      (nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
        targetPlaquette).mpr
        ((existsLimitObservables_iff_allSurfaces beta hBeta distance sourcePlaquette
          targetPlaquette).mp hExists)

/-- Nonempty receipts are equivalent to the construction-level API surface. -/
theorem nonempty_receipt_iff_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) ↔
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · intro hReceipt
    exact
      allSurfaces_existsConstruction beta hBeta distance sourcePlaquette
        targetPlaquette
        ((nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
          targetPlaquette).mp hReceipt)
  · intro hExists
    exact
      (nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
        targetPlaquette).mpr
        ((existsConstruction_iff_allSurfaces beta hBeta distance sourcePlaquette
          targetPlaquette).mp hExists)

/-- Nonempty receipts are equivalent to the expanded package-with-bound surface. -/
theorem nonempty_receipt_iff_existsPackageConnectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) ↔
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
  exact
    nonempty_receipt_iff_existsConstruction beta hBeta distance sourcePlaquette
      targetPlaquette

/-- Explicit façade data give the combined surface through the receipt. -/
theorem allSurfaces_ofData_via_receipt
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
    AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette :=
  allSurfaces beta hBeta distance sourcePlaquette targetPlaquette
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data give the nonempty construction package surface through
the receipt. -/
theorem nonemptyConstruction_ofData_via_receipt
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
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).nonempty

/-- Explicit façade data give the weak-limit/observable existential surface
through the receipt. -/
theorem existsLimitObservables_ofData_via_receipt
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
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).existsLimitObservables

/-- Explicit façade data give the construction-level API surface through the
receipt. -/
theorem existsConstruction_ofData_via_receipt
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
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).existsConstruction

/-- Explicit façade data give the expanded package-with-bound surface through
the receipt.

This theorem remains a receipt/API surface for the compact infinite-lattice
binary carrier.  It keeps the all-volume plaquette distance hypothesis and
finite-volume clustering certificate as hypotheses, and it does not assert a
continuum construction, Hamiltonian spectral gap, physical mass gap, or an
unconditional proof of the four-dimensional Yang--Mills mass gap problem. -/
theorem existsPackageConnectedCorrelation_abs_le_ofData_via_receipt
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
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).existsPackageConnectedCorrelation_abs_le

end AllSurfaceReceipt
end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
