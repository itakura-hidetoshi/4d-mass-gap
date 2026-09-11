import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringFacadeReceipt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A constructed compact infinite-lattice `Z₂` plaquette-clustering package.

The package records the selected Prokhorov subsequential weak limit, the two
local binary plaquette observables, their identification with the explicit
integer-lattice source and target plaquettes, and the exponential connected-
correlation bound.

This is a construction package inside the already formalized compact
infinite-lattice binary carrier.  It does not construct a continuum `ℝ⁴`
gauge-field configuration space, DLR state, reflection-positivity limit, OS
reconstruction, transfer matrix, Hamiltonian spectral gap, physical mass gap, or
an unconditional proof of the four-dimensional Yang--Mills mass gap problem. -/
structure z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) where
  prokhorovLimit :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding
  sourceObservable :
    BoundedContinuousFunction Z2InfiniteHypercubicBinaryConfiguration ℝ
  targetObservable :
    BoundedContinuousFunction Z2InfiniteHypercubicBinaryConfiguration ℝ
  sourceObservable_eq :
    sourceObservable = z2InfiniteHypercubicPlaquetteObservable sourcePlaquette
  targetObservable_eq :
    targetObservable = z2InfiniteHypercubicPlaquetteObservable targetPlaquette
  connectedCorrelation_abs_le :
    abs (prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        sourceObservable targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ))

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- Build the compact infinite-lattice `Z₂` plaquette-clustering construction
package from explicit façade data. -/
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
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
      beta hBeta distance sourcePlaquette targetPlaquette :=
  { prokhorovLimit :=
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K).prokhorovLimit
    sourceObservable := z2InfiniteHypercubicPlaquetteObservable sourcePlaquette
    targetObservable := z2InfiniteHypercubicPlaquetteObservable targetPlaquette
    sourceObservable_eq := rfl
    targetObservable_eq := rfl
    connectedCorrelation_abs_le := by
      exact
        z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_plaquetteObservable_connectedCorrelation_abs_le
          beta hBeta distance sourcePlaquette targetPlaquette hDistance K }

/-- The explicit data produce a nonempty construction package. -/
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
    Nonempty
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
        beta hBeta distance sourcePlaquette targetPlaquette) :=
  ⟨ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K⟩

/-- The construction package built from explicit data uses the source plaquette
observable. -/
theorem ofData_sourceObservable_eq
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
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable =
      z2InfiniteHypercubicPlaquetteObservable sourcePlaquette :=
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable_eq

/-- The construction package built from explicit data uses the target plaquette
observable. -/
theorem ofData_targetObservable_eq
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
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable =
      z2InfiniteHypercubicPlaquetteObservable targetPlaquette :=
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable_eq

/-- The construction package built from explicit data carries the exponential
connected-correlation bound. -/
theorem ofData_connectedCorrelation_abs_le
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
    abs ((ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable
        (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).connectedCorrelation_abs_le

/-- Existential construction surface: from the explicit façade data one obtains a
selected Prokhorov weak limit, the two local binary plaquette observables, and
the exponential connected-correlation bound. -/
theorem exists_limit_observables_connectedCorrelation_abs_le
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
    ∃ (prokhorovLimit :
        PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
          (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding),
      ∃ (sourceObservable targetObservable :
          BoundedContinuousFunction Z2InfiniteHypercubicBinaryConfiguration ℝ),
        sourceObservable = z2InfiniteHypercubicPlaquetteObservable sourcePlaquette ∧
          targetObservable = z2InfiniteHypercubicPlaquetteObservable targetPlaquette ∧
            abs (prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
                sourceObservable targetObservable) ≤
              z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
                Real.exp
                  (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
                    (distance : ℝ)) := by
  refine
    ⟨(ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).prokhorovLimit,
      z2InfiniteHypercubicPlaquetteObservable sourcePlaquette,
      z2InfiniteHypercubicPlaquetteObservable targetPlaquette, rfl, rfl, ?_⟩
  exact
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceiptOfData_plaquetteObservable_connectedCorrelation_abs_le
      beta hBeta distance sourcePlaquette targetPlaquette hDistance K

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
