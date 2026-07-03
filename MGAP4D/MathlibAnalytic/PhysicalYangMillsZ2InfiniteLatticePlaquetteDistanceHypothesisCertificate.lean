import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteFilterSeparationCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- An all-volume periodic distance hypothesis gives a `Filter.atTop` eventual
separation statement by `eventually_of_forall`.

This is a pure lattice-geometric repackaging of the finite-periodic distance
hypothesis.  It adds no continuum `ℝ⁴` gauge-field, DLR, reflection-positivity,
Hamiltonian, or mass-gap content. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation_of_distanceHypothesis
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
      distance p q := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation]
    using (eventually_of_forall hDistance)

/-- An all-volume periodic distance hypothesis audits any finite prefix. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit_of_distanceHypothesis
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q)
    (tailStart : ℕ) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
      distance p q tailStart := by
  intro k _hk
  exact hDistance k

/-- Build the bundled filter/finite-prefix separation certificate from the raw
all-volume distance hypothesis. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfDistanceHypothesis
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
      distance p q := by
  let hEventual :=
    z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation_of_distanceHypothesis
      hDistance
  exact
    { eventually_eq := hEventual
      finitePrefixAudit :=
        z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit_of_distanceHypothesis
          hDistance
          (z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
            hEventual) }

/-- Canonical concrete plaquette data obtained from the bundled certificate that
is itself generated from the raw all-volume distance hypothesis. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteDataOfDistanceHypothesisCertificate
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
  z2PeriodicHypercubicInfiniteLatticePlaquetteDataOfFilterSeparationCertificate
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfDistanceHypothesis
      hDistance)

/-- The selected Prokhorov subsequential weak limit obtained through the bundled
filter/finite-prefix certificate generated from the raw distance hypothesis. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfDistanceHypothesisCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificate
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfDistanceHypothesis
      hDistance)

/-- The concrete connected-correlation bound can also be invoked through the
bundled certificate generated from the raw all-volume distance hypothesis. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_distanceHypothesisCertificate
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
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfDistanceHypothesisCertificate
      beta hBeta distance p q hDistance).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfDistanceHypothesisCertificate] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_filterSeparationCertificate
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfDistanceHypothesis
        hDistance)
      K

end

end MathlibAnalytic
end MGAP4D
