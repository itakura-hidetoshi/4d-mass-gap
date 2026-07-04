import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringSurfaceEquivalence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- Combined surface for the compact infinite-lattice `Z₂` plaquette-clustering
construction.

The surface records, simultaneously, that the construction package is nonempty,
that the weak-limit/observable existential surface holds, and that the
construction-level API surface holds. -/
def AllSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) : Prop :=
  Nonempty
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
        beta hBeta distance sourcePlaquette targetPlaquette) ∧
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette ∧
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette

/-- Nonempty construction packages yield all API surfaces. -/
theorem allSurfaces_of_nonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) →
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette := by
  intro h
  refine ⟨h, ?_, ?_⟩
  · exact
      existsLimitObservables_of_nonempty beta hBeta distance sourcePlaquette
        targetPlaquette h
  · exact
      z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_of_nonempty
        beta hBeta distance sourcePlaquette targetPlaquette h

/-- All API surfaces yield nonempty construction packages. -/
theorem nonempty_of_allSurfaces
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

/-- Nonempty construction packages are equivalent to the combined API surface. -/
theorem nonempty_iff_allSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
          beta hBeta distance sourcePlaquette targetPlaquette) ↔
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · exact allSurfaces_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
  · exact nonempty_of_allSurfaces beta hBeta distance sourcePlaquette targetPlaquette

/-- The weak-limit/observable existential surface is equivalent to the combined
API surface. -/
theorem existsLimitObservables_iff_allSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsLimitObservables beta hBeta distance sourcePlaquette targetPlaquette ↔
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · intro h
    exact
      allSurfaces_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
        (nonempty_of_existsLimitObservables beta hBeta distance sourcePlaquette
          targetPlaquette h)
  · intro h
    exact h.2.1

/-- The construction-level API surface is equivalent to the combined API
surface. -/
theorem existsConstruction_iff_allSurfaces
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction
        beta hBeta distance sourcePlaquette targetPlaquette ↔
      AllSurfaces beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · intro h
    exact
      allSurfaces_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
        (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringNonempty_of_existsConstruction
          beta hBeta distance sourcePlaquette targetPlaquette h)
  · intro h
    exact h.2.2

/-- Explicit façade data yield the combined surface for the compact
infinite-lattice `Z₂` plaquette-clustering construction.

This theorem only packages already formalized compact-carrier data.  It keeps the
all-volume plaquette distance hypothesis and the finite-volume clustering
certificate as hypotheses, and it does not assert a continuum construction,
Hamiltonian spectral gap, physical mass gap, or an unconditional proof of the
four-dimensional Yang--Mills mass gap problem. -/
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
  allSurfaces_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
    (nonempty_ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

/-- Explicit façade data yield the combined surface through the weak-limit
existential surface. -/
theorem allSurfaces_ofData_via_existsLimitObservables
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
  (existsLimitObservables_iff_allSurfaces beta hBeta distance sourcePlaquette
    targetPlaquette).mp
      (existsLimitObservables_ofData beta hBeta distance sourcePlaquette targetPlaquette
        hDistance K)

/-- Explicit façade data yield the combined surface through the construction API
surface. -/
theorem allSurfaces_ofData_via_existsConstruction
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
  (existsConstruction_iff_allSurfaces beta hBeta distance sourcePlaquette
    targetPlaquette).mp
      (z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringExistsConstruction_ofData
        beta hBeta distance sourcePlaquette targetPlaquette hDistance K)

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
