import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringAllSurfaceReceiptEquivalence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- Public surface asserting the existence of a receipt for the compact
infinite-lattice `Z₂` plaquette-clustering API.

This is a thin naming layer over `Nonempty AllSurfaceReceipt`, intended as a
stable public API surface.  It does not add assumptions or strengthen the
formalized statement beyond the existing receipt package. -/
def ExistsAllSurfaceReceipt
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) : Prop :=
  Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette)

namespace ExistsAllSurfaceReceipt

/-- The public receipt surface is equivalent to nonempty receipts. -/
theorem iff_nonempty_receipt
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette ↔
      Nonempty (AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) :=
  Iff.rfl

/-- The public receipt surface is equivalent to the combined API surface. -/
theorem iff_allSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette ↔
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette :=
  AllSurfaceReceipt.nonempty_receipt_iff_allSurfaces beta hBeta distance sourcePlaquette
    targetPlaquette

/-- The public receipt surface is equivalent to nonempty construction packages. -/
theorem iff_nonemptyConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette ↔
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) :=
  AllSurfaceReceipt.nonempty_receipt_iff_nonemptyConstruction beta hBeta distance
    sourcePlaquette targetPlaquette

/-- The public receipt surface is equivalent to the weak-limit/observable
existential surface. -/
theorem iff_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette ↔
      ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette :=
  AllSurfaceReceipt.nonempty_receipt_iff_existsLimitObservables beta hBeta distance
    sourcePlaquette targetPlaquette

/-- The public receipt surface is equivalent to the construction-level API
surface. -/
theorem iff_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette ↔
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette :=
  AllSurfaceReceipt.nonempty_receipt_iff_existsConstruction beta hBeta distance
    sourcePlaquette targetPlaquette

/-- The public receipt surface is equivalent to the expanded package-with-bound
surface. -/
theorem iff_existsPackageConnectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette ↔
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
  AllSurfaceReceipt.nonempty_receipt_iff_existsPackageConnectedCorrelation_abs_le
    beta hBeta distance sourcePlaquette targetPlaquette

/-- Explicit façade data produce the public receipt surface.

This theorem keeps the all-volume plaquette distance hypothesis and finite-volume
clustering certificate as hypotheses.  It does not assert a continuum
configuration space, DLR state, reflection positivity, OS reconstruction,
transfer matrix, Hamiltonian spectral gap, physical mass gap, or an
unconditional proof of the four-dimensional Yang--Mills mass gap problem. -/
theorem ofData
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
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette :=
  AllSurfaceReceipt.nonempty_ofData beta hBeta distance sourcePlaquette
    targetPlaquette hDistance K

/-- Explicit façade data yield the combined surface through the public receipt
surface. -/
theorem allSurfaces_ofData
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
  (iff_allSurfaces beta hBeta distance sourcePlaquette targetPlaquette).mp
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data yield the construction-level API surface through the
public receipt surface. -/
theorem existsConstruction_ofData
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
  (iff_existsConstruction beta hBeta distance sourcePlaquette targetPlaquette).mp
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data yield the expanded package-with-bound surface through
the public receipt surface. -/
theorem existsPackageConnectedCorrelation_abs_le_ofData
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
  (iff_existsPackageConnectedCorrelation_abs_le beta hBeta distance sourcePlaquette
    targetPlaquette).mp
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

end ExistsAllSurfaceReceipt

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
