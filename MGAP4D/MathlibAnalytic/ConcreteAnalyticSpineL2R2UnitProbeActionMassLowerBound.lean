import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2UnitProbeUnboundednessCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Singleton squared mass of the diagonal action on the obstruction-selected unit
probe, measured only at the selected witness coordinate. -/
def concreteL2R2ObstructionActionSingletonSquaredMass (k : ℕ) : ℝ :=
  Finset.sum ({concreteL2DiagonalUnboundednessObstructionSurface.witness k} : Finset ℕ)
    (fun n : ℕ =>
      (concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k) n) ^ 2)

/-- The singleton action mass is exactly the square of the selected action
coordinate. -/
theorem concrete_l2_r2_obstruction_action_singleton_squared_mass_eq_selected_square
    (k : ℕ) :
    concreteL2R2ObstructionActionSingletonSquaredMass k =
      (concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)) ^ 2 := by
  simp [concreteL2R2ObstructionActionSingletonSquaredMass]

/-- The selected action coordinate has square larger than the threshold square. -/
theorem concrete_l2_r2_obstruction_action_selected_square_gt_threshold_square
    (k : ℕ) :
    (k : ℝ) ^ 2 <
      (concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)) ^ 2 := by
  have h := concrete_l2_obstruction_unit_action_threshold_law k
  have hk : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.zero_le k
  nlinarith

/-- The singleton squared mass of the action on the obstruction unit exceeds the
threshold square. -/
theorem concrete_l2_r2_obstruction_action_singleton_squared_mass_gt_threshold_square
    (k : ℕ) :
    (k : ℝ) ^ 2 < concreteL2R2ObstructionActionSingletonSquaredMass k := by
  rw [concrete_l2_r2_obstruction_action_singleton_squared_mass_eq_selected_square]
  exact concrete_l2_r2_obstruction_action_selected_square_gt_threshold_square k

/-- Public predicate for the finite-support action-mass lower-bound certificate. -/
def concreteL2R2UnitProbeActionMassLowerBoundCertificate : Prop :=
  ∀ k : ℕ,
    (k : ℝ) ^ 2 < concreteL2R2ObstructionActionSingletonSquaredMass k

/-- The finite-support action-mass lower-bound certificate is ready. -/
theorem concrete_l2_r2_unit_probe_action_mass_lower_bound_certificate :
    concreteL2R2UnitProbeActionMassLowerBoundCertificate := by
  intro k
  exact concrete_l2_r2_obstruction_action_singleton_squared_mass_gt_threshold_square k

/-- Public theorem-entry predicate for the action-mass lower-bound layer. -/
def concreteAnalyticSpineL2R2UnitProbeActionMassLowerBoundReady : Prop :=
  concreteAnalyticSpineL2R2UnitProbeUnboundednessCertificateReady ∧
  concreteL2R2UnitProbeActionMassLowerBoundCertificate

/-- The R2 unit-probe action-mass lower-bound layer is ready. -/
theorem concrete_analytic_spine_l2_r2_unit_probe_action_mass_lower_bound_ready :
    concreteAnalyticSpineL2R2UnitProbeActionMassLowerBoundReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_unit_probe_unboundedness_certificate_ready,
    concrete_l2_r2_unit_probe_action_mass_lower_bound_certificate⟩

end

end MathlibAnalytic
end MGAP4D
