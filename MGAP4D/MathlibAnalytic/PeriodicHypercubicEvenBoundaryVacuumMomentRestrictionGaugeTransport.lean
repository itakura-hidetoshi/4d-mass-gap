import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentGaugeInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance restrictedBoundaryVacuumGaugeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- The finite Wilson OS boundary vacuum moment pulled back to the actual full
finite `SU(N)` configuration through the canonical boundary restriction.

This is a raw full-configuration observable.  It stores no additional gauge
invariance assumption: its invariance is inherited from the actual boundary
restriction square and the already constructed boundary vacuum theorem. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryVacuumMoment
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenBoundaryVacuumMoment
    H N hN beta hbeta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)

/-- The raw full-configuration pullback of the finite Wilson OS boundary
vacuum moment is gauge invariant.

The only transport step is the canonical boundary restriction square

`boundaryRestriction (gaugeTransform gamma A)
  = boundaryGaugeTransform gamma (boundaryRestriction A)`.

After that rewrite, gauge invariance is exactly the previously generated
boundary vacuum theorem. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMoment_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta A := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let A₁ : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform gamma A
  have hB :
      P.boundaryRestriction A₁ =
        periodicHypercubicEvenBoundaryGaugeTransform H N gamma
          (P.boundaryRestriction A) := by
    dsimp [A₁]
    simpa [P] using
      (periodicHypercubicEven_boundaryRestriction_gaugeTransform
        H N hN beta hbeta gamma A)
  change
    periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta (P.boundaryRestriction A₁) =
      periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta (P.boundaryRestriction A)
  rw [hB]
  exact periodicHypercubicEvenBoundaryVacuumMoment_gaugeInvariant
    H N hN beta hbeta gamma (P.boundaryRestriction A)

/-- Functional form of the raw boundary-vacuum restriction transport.  This is
suited to later actual-analysis and interpolation rewrites. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMoment_comp_gaugeTransform
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (fun A : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A)) =
      fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta A := by
  funext A
  exact periodicHypercubicEvenRestrictedBoundaryVacuumMoment_gaugeInvariant
    H N hN beta hbeta gamma A

end

end MathlibAnalytic
end MGAP4D
