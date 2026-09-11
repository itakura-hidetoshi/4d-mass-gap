import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureGaugeInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance restrictedBoundaryGramGaugeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- The completed-positive boundary Gram feature pulled back to the actual full
finite `SU(N)` configuration through the canonical boundary and positive-half
restriction maps.

This is the raw full-configuration feature needed by downstream actual-analysis
bridges: no new gauge action or invariance hypothesis is stored here. -/
noncomputable def periodicHypercubicEvenRestrictedCompletedPositiveGramFeature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)
    ((periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A)

/-- The raw completed-positive Gram feature on the actual full finite
configuration space is gauge invariant.

The proof is entirely kinematic plus the previously generated boundary-feature
invariance: both canonical restrictions commute with the actual finite gauge
transform, after which the simultaneous boundary/open-half gauge action is
removed. -/
theorem periodicHypercubicEvenRestrictedCompletedPositiveGramFeature_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedCompletedPositiveGramFeature
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenRestrictedCompletedPositiveGramFeature
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
  have hX :
      P.positiveRestriction A₁ =
        periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma
          (P.positiveRestriction A) := by
    dsimp [A₁]
    simpa [P] using
      (periodicHypercubicEven_positiveRestriction_gaugeTransform
        H N hN beta hbeta gamma A)
  change
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta
        (P.boundaryRestriction A₁)
        (P.positiveRestriction A₁) =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta
        (P.boundaryRestriction A)
        (P.positiveRestriction A)
  rw [hB, hX]
  exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaugeInvariant
    H N hN beta hbeta gamma (P.boundaryRestriction A) (P.positiveRestriction A)

/-- Functional form of raw restriction gauge transport.  Downstream
interpolation/Tietze arguments can rewrite the whole finite-volume feature in
one step instead of separately transporting boundary and open-half
coordinates. -/
theorem periodicHypercubicEvenRestrictedCompletedPositiveGramFeature_comp_gaugeTransform
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (fun A : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenRestrictedCompletedPositiveGramFeature
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A)) =
      fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenRestrictedCompletedPositiveGramFeature
          H N hN beta hbeta A := by
  funext A
  exact periodicHypercubicEvenRestrictedCompletedPositiveGramFeature_gaugeInvariant
    H N hN beta hbeta gamma A

end

end MathlibAnalytic
end MGAP4D
