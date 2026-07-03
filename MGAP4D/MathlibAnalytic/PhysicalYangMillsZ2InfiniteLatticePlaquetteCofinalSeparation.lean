import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClustering
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The periodic base-distance obtained by reducing two fixed integer-lattice
plaquettes into the `k`-th canonical periodic volume.

This is only a lattice-geometric distance on the finite periodic reduction.  It
is not a physical spacetime distance and carries no Hamiltonian or mass-gap
content. -/
def z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance
    (p q : IntegerHypercubicPlaquette)
    (k : ℕ) : ℕ :=
  periodicHypercubicPlaquetteBaseL1Distance
    (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
    (integerHypercubicPlaquetteToPeriodic
      (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) p)
    (integerHypercubicPlaquetteToPeriodic
      (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) q)

/-- The distance hypothesis used by the concrete infinite-lattice clustering
bridge is definitionally the assertion that the reduced periodic distance is the
same at every canonical volume. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_iff
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q ↔
      ∀ k : ℕ,
        z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
          distance :=
  Iff.rfl

/-- A finite-prefix plus cofinal-tail certificate for the all-volume periodic
separation hypothesis.

The `tailStart` field marks the first volume index from which the no-wraparound
or cofinal geometry argument is expected to apply.  The finitely many earlier
indices are handled separately by `prefix_eq`. -/
structure z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette) where
  tailStart : ℕ
  prefix_eq :
    ∀ k : ℕ,
      k < tailStart →
        z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
          distance
  tail_eq :
    ∀ k : ℕ,
      tailStart ≤ k →
        z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
          distance

/-- A cofinal-tail certificate together with the finite prefix audit supplies the
all-volume distance hypothesis required by the existing Prokhorov clustering
chain. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_cofinalSeparation
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
        distance p q) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
      distance p q := by
  intro k
  by_cases hk : k < C.tailStart
  · simpa [z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance] using
      C.prefix_eq k hk
  · have hkTail : C.tailStart ≤ k := le_of_not_gt hk
    simpa [z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance] using
      C.tail_eq k hkTail

/-- Build the concrete canonical plaquette data from a finite-prefix/cofinal-tail
separation certificate. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteDataOfCofinalSeparation
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
        distance p q) :
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta)
      distance :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteData
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_cofinalSeparation C)

/-- The selected Prokhorov subsequential weak limit attached to a concrete
plaquette pair and a finite-prefix/cofinal-tail separation certificate. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfCofinalSeparation
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
        distance p q) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimit
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_cofinalSeparation C)

/-- The concrete connected-correlation bound can be invoked from the
finite-prefix/cofinal-tail separation certificate rather than a raw all-volume
hypothesis. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_cofinalSeparation
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
        distance p q)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfCofinalSeparation
      beta hBeta distance p q C).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfCofinalSeparation] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_cofinalSeparation C)
      K

end

end MathlibAnalytic
end MGAP4D
