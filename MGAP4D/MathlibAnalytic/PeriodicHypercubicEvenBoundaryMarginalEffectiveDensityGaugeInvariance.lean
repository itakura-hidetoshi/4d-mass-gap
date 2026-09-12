import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentGaugeInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance boundaryEffectiveDensityGaugeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- The actual finite Wilson effective boundary density is invariant under the
boundary gauge action induced from a finite lattice gauge transformation.

The density is definitionally the `ENNReal.ofReal` image of the square of the
boundary vacuum moment, so invariance is inherited constructively from the
already generated vacuum-moment theorem. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b) =
      periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryMarginalEffectiveDensity
  rw [periodicHypercubicEvenBoundaryVacuumMoment_gaugeInvariant
    H N hN beta hbeta gamma b]

/-- Pull the effective Wilson boundary density back to the actual full finite
`SU(N)` configuration through the canonical boundary restriction. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ENNReal :=
  periodicHypercubicEvenBoundaryMarginalEffectiveDensity
    H N hN beta hbeta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)

/-- The actual full-configuration pullback of the finite Wilson effective
boundary density is gauge invariant.

This closes the raw density transport square without adding an interpolation
or gauge-invariance assumption: the canonical boundary restriction commutes
with the finite gauge transform and the boundary density is already fixed by
the induced boundary action. -/
theorem periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity
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
    periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta (P.boundaryRestriction A₁) =
      periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta (P.boundaryRestriction A)
  rw [hB]
  exact periodicHypercubicEvenBoundaryMarginalEffectiveDensity_gaugeInvariant
    H N hN beta hbeta gamma (P.boundaryRestriction A)

/-- Functional form of the raw effective-density restriction transport. -/
theorem periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity_comp_gaugeTransform
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (fun A : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A)) =
      fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity
          H N hN beta hbeta A := by
  funext A
  exact periodicHypercubicEvenRestrictedBoundaryMarginalEffectiveDensity_gaugeInvariant
    H N hN beta hbeta gamma A

end

end MathlibAnalytic
end MGAP4D
