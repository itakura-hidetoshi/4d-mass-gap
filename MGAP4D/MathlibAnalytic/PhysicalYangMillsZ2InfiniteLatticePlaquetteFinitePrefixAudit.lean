import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteFilterSeparation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A finite-prefix audit of the reduced periodic plaquette distance, expressed
as a `Finset.range` check.

This records exactly the finitely many volume indices before a cofinal tail
starts.  It is a finite lattice-geometric audit, not a continuum `ℝ⁴` gauge-field
or Hamiltonian assertion. -/
def z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (tailStart : ℕ) : Prop :=
  ∀ k : ℕ,
    k ∈ Finset.range tailStart →
      z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
        distance

/-- The `Finset.range` finite-prefix audit is the same as the ordinary
`k < tailStart` prefix statement used by the previous certificate layer. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit_iff_forall_lt
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (tailStart : ℕ) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
        distance p q tailStart ↔
      ∀ k : ℕ,
        k < tailStart →
          z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
            distance := by
  classical
  constructor
  · intro h k hk
    exact h k (Finset.mem_range.mpr hk)
  · intro h k hk
    exact h k (Finset.mem_range.mp hk)

/-- A `Finset.range` finite-prefix audit supplies the prefix function expected by
`z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventually`. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquettePrefix_of_finitePrefixAudit
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    {tailStart : ℕ}
    (hAudit :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
        distance p q tailStart) :
    ∀ k : ℕ,
      k < tailStart →
        z2PeriodicHypercubicInfiniteLatticePlaquettePeriodicDistance p q k =
          distance :=
  (z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit_iff_forall_lt
    distance p q tailStart).mp hAudit

/-- Build the finite-prefix/cofinal-tail certificate from a filter-eventual
separation proof and a `Finset.range` audit of the chosen finite prefix. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventuallyFinitePrefix
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q)
    (hAudit :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
        distance p q
        (z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
          hEventual)) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificate
      distance p q :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventually
    hEventual
    ((z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit_iff_forall_lt
      distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
        hEventual)).mp hAudit)

/-- A filter-eventual separation proof plus a finite `Finset.range` prefix audit
supplies the all-volume distance hypothesis required by the canonical Prokhorov
clustering chain. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_filterEventuallyFinitePrefix
    {distance : ℕ}
    {p q : IntegerHypercubicPlaquette}
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q)
    (hAudit :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
        distance p q
        (z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
          hEventual)) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
      distance p q :=
  z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis_of_cofinalSeparation
    (z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventuallyFinitePrefix
      hEventual hAudit)

/-- The concrete connected-correlation bound can be invoked directly from an
`atTop` eventual-separation proof and a finite `Finset.range` prefix audit. -/
theorem z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_filterEventuallyFinitePrefix
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (p q : IntegerHypercubicPlaquette)
    (hEventual :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFilterEventuallySeparation
        distance p q)
    (hAudit :
      z2PeriodicHypercubicInfiniteLatticePlaquetteFinitePrefixAudit
        distance p q
        (z2PeriodicHypercubicInfiniteLatticePlaquetteEventualTailStart
          hEventual))
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((z2PeriodicHypercubicInfiniteLatticePlaquetteProkhorovLimitOfCofinalSeparation
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventuallyFinitePrefix
        hEventual hAudit)).toWeakLimit.continuumConnectedCorrelation
        (z2InfiniteHypercubicPlaquetteObservable p)
        (z2InfiniteHypercubicPlaquetteObservable q)) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  simpa using
    z2PeriodicHypercubicInfiniteLatticePlaquetteConnectedCorrelation_abs_le_of_cofinalSeparation
      beta hBeta distance p q
      (z2PeriodicHypercubicInfiniteLatticePlaquetteCofinalSeparationCertificateOfFilterEventuallyFinitePrefix
        hEventual hAudit)
      K

end

end MathlibAnalytic
end MGAP4D
