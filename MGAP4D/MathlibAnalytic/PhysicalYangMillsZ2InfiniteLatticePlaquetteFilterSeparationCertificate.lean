import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteFinitePrefixAudit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A bundled `Filter.atTop`/finite-prefix separation certificate for two fixed
integer-lattice plaquettes.

The first field records the eventual constant reduced periodic distance along
the canonical volume schedule.  The second field records the finite audit of the
prefix before the chosen tail start, using `Finset.range`.

This is only a lattice-geometric separation certificate for the compact
infinite-lattice binary carrier.  It is not a continuum `ℝ⁴` gauge-field, DLR,
reflection-positivity, Hamiltonian, or mass-gap construction. -/
structure z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette) where
  eventually_eq :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
      distance p q
  finitePrefixAudit :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
      distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
        eventually_eq)

/-- The cofinal-tail certificate extracted from the bundled filter/finite-prefix
separation certificate. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate.toCofinalSeparationCertificate
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
      distance p q :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventuallyFinitePrefix
    C.eventually_eq C.finitePrefixAudit

/-- The all-volume distance hypothesis extracted from the bundled
filter/finite-prefix separation certificate. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterSeparationCertificate
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
      distance p q :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterEventuallyFinitePrefix
    C.eventually_eq C.finitePrefixAudit

/-- Build the concrete canonical plaquette data from the bundled filter/finite
prefix separation certificate. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteDataOfFilterSeparationCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q) :
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta)
      distance :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteData
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterSeparationCertificate C)

/-- The selected Prokhorov subsequential weak limit attached to a concrete
plaquette pair and a bundled filter/finite-prefix separation certificate. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimit
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterSeparationCertificate C)

/-- The concrete connected-correlation bound invoked from the bundled
filter/finite-prefix separation certificate. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_filterSeparationCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (C :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificate
      beta hBeta distance p q C).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificate] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterSeparationCertificate C)
      K

end

end MathlibAnalytic
end MGAP4D
