import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalOperatorEvidence
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2HilbertNormOneTarget

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Unit-probe unboundedness certificate for the concrete R2 diagonal action.

For every threshold `k`, the obstruction-selected coordinate unit has
finite-support norm squared equal to `1`, while the diagonal action at the
selected coordinate exceeds `k`.

This is not yet the completed Hilbert-space operator-norm unboundedness theorem;
it is the concrete unit-probe certificate from which that theorem should later be
promoted once the completed norm bridge is available. -/
def concreteL2R2UnitProbeUnboundednessCertificate : Prop :=
  ∀ k : ℕ,
    concreteL2UnitFiniteSupportNormSq
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k) = 1 ∧
    (k : ℝ) <
      concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- The R2 unit-probe unboundedness certificate is proved from the finite-support
norm-squared unit law and the obstruction unit action threshold law. -/
theorem concrete_l2_r2_unit_probe_unboundedness_certificate :
    concreteL2R2UnitProbeUnboundednessCertificate := by
  intro k
  exact ⟨
    concrete_l2_unit_finite_support_norm_sq_eq_one
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k),
    concrete_l2_obstruction_unit_action_threshold_law k⟩

/-- Public theorem-entry predicate for the R2 unit-probe unboundedness layer. -/
def concreteAnalyticSpineL2R2UnitProbeUnboundednessCertificateReady : Prop :=
  concreteL2R2DiagonalOperatorEvidence ∧
  concreteL2UnitHilbertNormOneTarget ∧
  concreteL2R2UnitProbeUnboundednessCertificate

/-- The R2 unit-probe unboundedness certificate layer is ready. -/
theorem concrete_analytic_spine_l2_r2_unit_probe_unboundedness_certificate_ready :
    concreteAnalyticSpineL2R2UnitProbeUnboundednessCertificateReady := by
  exact ⟨
    concrete_l2_r2_diagonal_operator_evidence,
    concrete_l2_unit_hilbert_norm_one_target_from_norm_sq,
    concrete_l2_r2_unit_probe_unboundedness_certificate⟩

end

end MathlibAnalytic
end MGAP4D
