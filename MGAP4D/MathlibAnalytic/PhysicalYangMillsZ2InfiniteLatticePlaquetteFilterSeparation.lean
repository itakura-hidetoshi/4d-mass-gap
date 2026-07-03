import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteCofinalSeparation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The finite-periodic plaquette separation is eventually constant along the
canonical volume schedule, expressed with mathlib's `Filter.atTop`.

This is still only a statement about periodic reductions of fixed
integer-lattice plaquettes.  It does not assert any continuum `ℝ⁴` gauge-field
geometry or Hamiltonian spectral-gap property. -/
def z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette) : Prop :=
  ∀ᶠ k : ℕ in atTop,
    z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
      distance

/-- The filter eventual-separation statement is exactly an ordinary cofinal-tail
statement on `ℕ`. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation_iff_exists_tail
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q ↔
      ∃ tailStart : ℕ,
        ∀ k : ℕ,
          tailStart ≤ k →
            z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
              distance := by
  simpa [z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation]
    using
      (eventually_atTop :
        ((∀ᶠ k : ℕ in atTop,
          z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
            distance) ↔
          ∃ tailStart : ℕ,
            ∀ k : ℕ,
              tailStart ≤ k →
                z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
                  distance))

/-- The chosen first index of the cofinal tail supplied by an `atTop` eventual
separation proof. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q) : ℕ :=
  Classical.choose
    ((z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation_iff_exists_tail
      distance p q).mp hEventual)

/-- The chosen tail start indeed bounds a constant-distance tail. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart_spec
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q) :
    ∀ k : ℕ,
      z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart hEventual ≤ k →
        z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
          distance :=
  Classical.choose_spec
    ((z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation_iff_exists_tail
      distance p q).mp hEventual)

/-- A filter-eventual separation proof plus a finite-prefix audit supplies the
finite-prefix/cofinal-tail certificate used by the previous layer. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventually
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q)
    (hPrefix :
      ∀ k : ℕ,
        k < z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
          hEventual →
          z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
            distance) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
      distance p q :=
  { tailStart :=
      z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart hEventual
    prefix_eq := hPrefix
    tail_eq :=
      z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart_spec
        hEventual }

/-- A filter-eventual separation proof plus the finite-prefix audit gives the
raw all-volume distance hypothesis required by the canonical Prokhorov
clustering chain. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterEventually
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q)
    (hPrefix :
      ∀ k : ℕ,
        k < z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
          hEventual →
          z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
            distance) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
      distance p q :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_cofinalSeparation
    (z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventually
      hEventual hPrefix)

/-- The concrete connected-correlation bound can be invoked directly from a
mathlib `Filter.atTop` eventual-separation proof and a finite-prefix audit. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_filterEventually
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q)
    (hPrefix :
      ∀ k : ℕ,
        k < z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
          hEventual →
          z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
            distance)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfCofinalSeparation
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventually
        hEventual hPrefix)).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa using
    z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_cofinalSeparation
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventually
        hEventual hPrefix)
      K

end

end MathlibAnalytic
end MGAP4D
