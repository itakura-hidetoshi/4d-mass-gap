import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferFixedContourProjectorIdentification

/-!
# Regression tests for actual nearby top-projector identification

These tests require the literal Wilson operators, with no supplied continuity,
rank-persistence, or nearby-projector-equality hypotheses.
-/

namespace MGAP4D.MathlibAnalytic

open Filter Topology

noncomputable section

example (H N : ℕ) (hN : 0 < N) (beta0 : Set.Ici (0 : ℝ)) :
    ∀ᶠ beta in 𝓝 beta0,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2 := by
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_eq_cfcTopProjection
      H N hN beta0

example (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2) := by
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_halfLine_continuous
      H N hN

end
end MGAP4D.MathlibAnalytic
