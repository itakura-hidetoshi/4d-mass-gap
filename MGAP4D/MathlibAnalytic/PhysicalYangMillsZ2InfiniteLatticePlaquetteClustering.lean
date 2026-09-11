import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteObservable
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- The finite-periodic separation hypothesis for two fixed integer-lattice
plaquettes after reduction to every canonical periodic volume.

This is the explicit no-wraparound/cofinal-separation input.  It is a lattice
separation hypothesis only; it is not a continuum or Hamiltonian spectral-gap
assumption. -/
abbrev z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette) : Prop :=
  ∀ k : ℕ,
    periodicHypercubicPlaquetteBaseL1Distance
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        (integerHypercubicPlaquetteToPeriodic
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) p)
        (integerHypercubicPlaquetteToPeriodic
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) q) =
      distance

/-- A concrete pair of integer-lattice `Z₂` plaquette observables packaged as the
canonical finite-periodic plaquette data needed by the Prokhorov clustering
chain.

The common-space observables are the bounded continuous local observables on the
compact infinite-lattice binary carrier.  The finite plaquettes are their
periodic reductions in each canonical volume, and the pullback obligations are
closed by `z2InfiniteHypercubicPlaquetteObservable_pullback`. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteData
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q) :
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta)
      distance :=
  { sourceObservable := z2InfiniteHypercubicPlaquetteObservable p
    targetObservable := z2InfiniteHypercubicPlaquetteObservable q
    sourcePlaquette := fun k =>
      integerHypercubicPlaquetteToPeriodic
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) p
    targetPlaquette := fun k =>
      integerHypercubicPlaquetteToPeriodic
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) q
    distance_eq := hDistance
    source_pullback := fun k U => by
      simpa [z2PeriodicHypercubicInfiniteLatticeEmbedding,
        z2PeriodicHypercubicInfiniteLatticeInterpolation] using
        (z2InfiniteHypercubicPlaquetteObservable_pullback
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le p U)
    target_pullback := fun k U => by
      simpa [z2PeriodicHypercubicInfiniteLatticeEmbedding,
        z2PeriodicHypercubicInfiniteLatticeInterpolation] using
        (z2InfiniteHypercubicPlaquetteObservable_pullback
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le q U) }

/-- The selected Prokhorov subsequential weak limit attached to a concrete pair
of integer-lattice plaquette observables on the compact binary carrier. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimit
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding :=
  (z2PeriodicHypercubicInfiniteLatticePlaquetteData
    beta hBeta distance p q hDistance).prokhorovLimitOfTight
      (z2PeriodicHypercubicInfiniteLatticeEmbedding_isTight beta hBeta)

/-- For two fixed integer-lattice plaquettes whose finite-periodic reductions
remain at the declared separation, the selected Prokhorov weak limit has the
same explicit exponential connected-correlation bound as the finite-volume
canonical clustering certificate.

The weak limit here lives on the compact infinite integer-lattice binary
link-field carrier.  This theorem does not construct a continuum `ℝ⁴` gauge
field, a Hamiltonian, a spectral gap, or a physical mass gap. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimit
      beta hBeta distance p q hDistance).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimit,
    z2PeriodicHypercubicInfiniteLatticePlaquetteData] using
    (z2PeriodicHypercubicInfiniteLatticePlaquetteData
      beta hBeta distance p q hDistance).continuum_abs_le_of_tight
      K (z2PeriodicHypercubicInfiniteLatticeEmbedding_isTight beta hBeta)

end

end MathlibAnalytic
end MGAP4D
