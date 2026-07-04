import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringConstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- The existential surface corresponding to a compact infinite-lattice `Z₂`
plaquette-clustering construction package. -/
def ExistsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) : Prop :=
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
                  (distance : ℝ))

/-- A construction package yields its existential weak-limit and observable data. -/
theorem existsLimitObservables_of_nonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) →
      ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette := by
  rintro ⟨C⟩
  refine ⟨C.prokhorovLimit, C.sourceObservable, C.targetObservable, C.sourceObservable_eq,
    C.targetObservable_eq, ?_⟩
  exact C.connectedCorrelation_abs_le

/-- Existential weak-limit and observable data can be repackaged as a construction
package. -/
theorem nonempty_of_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette →
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) := by
  rintro ⟨prokhorovLimit, sourceObservable, targetObservable, hSource, hTarget, hBound⟩
  exact
    ⟨{ prokhorovLimit := prokhorovLimit
       sourceObservable := sourceObservable
       targetObservable := targetObservable
       sourceObservable_eq := hSource
       targetObservable_eq := hTarget
       connectedCorrelation_abs_le := hBound }⟩

/-- Nonempty construction packages are equivalent to the existential weak-limit
and observable surface. -/
theorem nonempty_iff_existsLimitObservables
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) ↔
      ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · exact
      existsLimitObservables_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
  · exact
      nonempty_of_existsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette

/-- The explicit façade data produce the existential weak-limit and observable
surface.

This is a repackaging theorem for the compact infinite-lattice binary carrier. It
keeps the supplied all-volume distance hypothesis and finite-volume clustering
certificate as hypotheses and does not assert a Hamiltonian spectral gap or a
physical mass gap. -/
theorem existsLimitObservables_ofData
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
  existsLimitObservables_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
    (nonempty_ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- The explicit façade data produce a nonempty construction package, expressed
through the nonempty/existential equivalence. -/
theorem nonempty_ofData_via_existsLimitObservables
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
  (nonempty_iff_existsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette).mpr
    (existsLimitObservables_ofData beta hBeta distance sourcePlaquette targetPlaquette
      hDistance K)

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
