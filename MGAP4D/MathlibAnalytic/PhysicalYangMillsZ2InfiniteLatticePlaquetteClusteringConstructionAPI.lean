import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringConstructionEquivalence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-level surface for compact infinite-lattice `Z₂` plaquette
clustering.

This proposition says that there is a constructed package whose source and
target observables are the two explicit local binary plaquette observables and
whose selected Prokhorov weak limit satisfies the exponential connected-
correlation bound. -/
def z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) : Prop :=
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

/-- Nonempty construction packages yield the construction-level API surface. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_of_nonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) →
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette := by
  rintro ⟨C⟩
  exact ⟨C, C.sourceObservable_eq, C.targetObservable_eq, C.connectedCorrelation_abs_le⟩

/-- The construction-level API surface yields a nonempty construction package. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringNonempty_of_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette →
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) := by
  rintro ⟨C, _hSource, _hTarget, _hBound⟩
  exact ⟨C⟩

/-- Nonempty construction packages are equivalent to the construction-level API
surface. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringNonempty_iff_existsConstruction
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) ↔
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · exact
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_of_nonempty
        beta hBeta distance sourcePlaquette targetPlaquette
  · exact
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringNonempty_of_existsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette

/-- Explicit façade data construct a compact infinite-lattice `Z₂` plaquette
clustering package satisfying the expanded construction-level API surface.

The all-volume plaquette distance hypothesis and the finite-volume clustering
certificate remain hypotheses.  This theorem does not construct continuum `ℝ⁴`
gauge fields, a DLR state, reflection positivity, OS reconstruction, a transfer
matrix, a Hamiltonian spectral gap, or a physical mass gap. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_ofData
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
      beta hBeta distance sourcePlaquette targetPlaquette := by
  exact
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_of_nonempty
      beta hBeta distance sourcePlaquette targetPlaquette
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction.nonempty_ofData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data construct a package, and the construction-level API
surface is obtained through the nonempty/API equivalence. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_ofData_via_iff
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
  (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringNonempty_iff_existsConstruction
    beta hBeta distance sourcePlaquette targetPlaquette).mp
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction.nonempty_ofData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

end

end MathlibAnalytic
end MGAP4D
