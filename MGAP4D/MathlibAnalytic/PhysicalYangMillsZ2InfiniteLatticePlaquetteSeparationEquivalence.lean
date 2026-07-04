import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteDistanceHypothesisCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Existence of a bundled filter/finite-prefix separation certificate is
logically equivalent to the raw all-volume periodic distance hypothesis.

This is a bookkeeping equivalence for concrete integer-lattice Z2 plaquette
observables on the compact infinite-lattice binary carrier.  It is not a
continuum `ℝ⁴` gauge-field, DLR, reflection-positivity, Hamiltonian, or mass-gap
construction. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate_nonempty_iff_distanceHypothesis
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette} :
    Nonempty
      (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q) ↔
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q := by
  constructor
  · rintro ⟨C⟩
    exact
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterSeparationCertificate
        C
  · intro hDistance
    exact
      ⟨z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfDistanceHypothesis
        hDistance⟩

/-- The raw all-volume distance hypothesis gives a nonempty bundled certificate
package. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate_nonempty_of_distanceHypothesis
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance p q) :
    Nonempty
      (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
        distance p q) :=
  (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate_nonempty_iff_distanceHypothesis).2
    hDistance

/-- A nonempty bundled certificate package recovers the raw all-volume distance
hypothesis. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterSeparationCertificate_nonempty
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hC :
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
          distance p q)) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
      distance p q :=
  (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate_nonempty_iff_distanceHypothesis).1
    hC

/-- Choose a bundled filter/finite-prefix separation certificate from its
nonempty existence proof. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfNonempty
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hC :
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
          distance p q)) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
      distance p q :=
  Classical.choice hC

/-- Canonical concrete plaquette data obtained from a nonempty bundled
separation-certificate package. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteDataOfFilterSeparationCertificateNonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hC :
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
          distance p q)) :
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta)
      distance :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteDataOfFilterSeparationCertificate
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfNonempty
      hC)

/-- The selected Prokhorov subsequential weak limit obtained from a nonempty
bundled separation-certificate package. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificateNonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hC :
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
          distance p q)) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificate
    beta hBeta distance p q
    (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfNonempty
      hC)

/-- The concrete connected-correlation bound invoked from nonempty existence of
the bundled filter/finite-prefix separation certificate. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_filterSeparationCertificateNonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hC :
      Nonempty
        (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificate
          distance p q))
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificateNonempty
      beta hBeta distance p q hC).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfFilterSeparationCertificateNonempty] using
    z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_filterSeparationCertificate
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteFilterSeparationCertificateOfNonempty
        hC)
      K

end

end MathlibAnalytic
end MGAP4D
