import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ProgressIndex

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The raw coordinate unit vector at index `k`. -/
def concreteL2UnitRaw (k : ℕ) : ℕ → ℝ :=
  fun n => if n = k then 1 else 0

/-- Unit raw vector has finite support. -/
def concreteL2UnitFiniteSupport (k : ℕ) : ConcreteL2RealFiniteSupport ⟨concreteL2UnitRaw k, by
    classical
    -- finite support gives square summability by reducing to the singleton support
    have hzero : ∀ n : ℕ, n ∉ ({k} : Finset ℕ) → (concreteL2UnitRaw k n) ^ 2 = 0 := by
      intro n hn
      simp [concreteL2UnitRaw, Finset.mem_singleton] at hn ⊢
      exact hn
    exact summable_of_ne_finset_zero hzero⟩ :=
  by
    exact ⟨{k}, by
      intro n hn
      simp [concreteL2UnitRaw, Finset.mem_singleton] at hn ⊢
      exact hn⟩

/-- The concrete `l2` unit vector at index `k`. -/
def concreteL2Unit (k : ℕ) : ConcreteL2RealSequence :=
  ⟨concreteL2UnitRaw k, by
    classical
    have hzero : ∀ n : ℕ, n ∉ ({k} : Finset ℕ) → (concreteL2UnitRaw k n) ^ 2 = 0 := by
      intro n hn
      simp [concreteL2UnitRaw, Finset.mem_singleton] at hn ⊢
      exact hn
    exact summable_of_ne_finset_zero hzero⟩

/-- The concrete unit vector has finite support. -/
def concreteL2UnitFiniteSupportWitness (k : ℕ) :
    ConcreteL2RealFiniteSupport (concreteL2Unit k) := by
  exact ⟨{k}, by
    intro n hn
    simp [concreteL2Unit, concreteL2UnitRaw, Finset.mem_singleton] at hn ⊢
    exact hn⟩

/-- The concrete unit vector belongs to the diagonal domain. -/
def concreteL2UnitDiagonalDomain (k : ℕ) : ConcreteL2DiagonalDomainCarrier :=
  ⟨concreteL2Unit k, by
    classical
    have hzero : ∀ n : ℕ, n ∉ ({k} : Finset ℕ) →
        concreteL2DiagonalWeight n *
          (concreteL2DiagonalWeight n *
            ((concreteL2Unit k).1 n * (concreteL2Unit k).1 n)) = 0 := by
      intro n hn
      simp [concreteL2Unit, concreteL2UnitRaw, Finset.mem_singleton] at hn ⊢
      exact hn
    simpa [ConcreteL2DiagonalDomain, pow_two, mul_assoc, mul_left_comm, mul_comm]
      using summable_of_ne_finset_zero hzero⟩

/-- The unit vector at index `k` is in the finite-support diagonal core. -/
def concreteL2UnitFiniteSupportCore (k : ℕ) :
    ConcreteL2DiagonalFiniteSupportDomainCarrier :=
  ⟨concreteL2UnitDiagonalDomain k, concreteL2UnitFiniteSupportWitness k⟩

/-- The diagonal raw action on the unit vector has value equal to the diagonal
weight at the selected coordinate. -/
theorem concrete_l2_diagonal_raw_action_unit_self (k : ℕ) :
    concreteL2DiagonalRawAction (concreteL2UnitDiagonalDomain k) k =
      concreteL2DiagonalWeight k := by
  simp [concreteL2DiagonalRawAction, concreteL2UnitDiagonalDomain,
    concreteL2Unit, concreteL2UnitRaw]

/-- The diagonal raw action on the unit vector vanishes away from the selected
coordinate. -/
theorem concrete_l2_diagonal_raw_action_unit_off (k n : ℕ) (h : n ≠ k) :
    concreteL2DiagonalRawAction (concreteL2UnitDiagonalDomain k) n = 0 := by
  simp [concreteL2DiagonalRawAction, concreteL2UnitDiagonalDomain,
    concreteL2Unit, concreteL2UnitRaw, h]

/-- Surface for concrete unit probes in the diagonal domain.  This is still not
an operator-norm unboundedness theorem, not a density theorem, not graph closure,
not a closed-operator theorem, and not self-adjointness. -/
structure ConcreteL2UnitProbeSurface where
  unit : ℕ → ConcreteL2RealSequence
  unitDomain : ℕ → ConcreteL2DiagonalDomainCarrier
  unitFiniteSupportCore : ℕ → ConcreteL2DiagonalFiniteSupportDomainCarrier
  actionSelfLaw : ∀ k : ℕ,
    concreteL2DiagonalRawAction (unitDomain k) k = concreteL2DiagonalWeight k
  actionOffLaw : ∀ k n : ℕ, n ≠ k →
    concreteL2DiagonalRawAction (unitDomain k) n = 0
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotDensityTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The concrete `l2` unit probe surface. -/
def concreteL2UnitProbeSurface : ConcreteL2UnitProbeSurface :=
  { unit := concreteL2Unit
    unitDomain := concreteL2UnitDiagonalDomain
    unitFiniteSupportCore := concreteL2UnitFiniteSupportCore
    actionSelfLaw := concrete_l2_diagonal_raw_action_unit_self
    actionOffLaw := concrete_l2_diagonal_raw_action_unit_off
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotDensityTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete `l2` unit probe surface. -/
def concreteAnalyticSpineL2UnitProbeSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2ProgressIndexSurfaceReady ∧
  (∀ k : ℕ,
    concreteL2DiagonalRawAction (concreteL2UnitDiagonalDomain k) k =
      concreteL2DiagonalWeight k) ∧
  concreteL2UnitProbeSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2UnitProbeSurface.boundaryNotDensityTheorem ∧
  concreteL2UnitProbeSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2UnitProbeSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the concrete `l2` unit probe surface. -/
theorem concrete_analytic_spine_l2_unit_probe_surface_ready :
    concreteAnalyticSpineL2UnitProbeSurfaceReady := by
  unfold concreteAnalyticSpineL2UnitProbeSurfaceReady
  exact And.intro concrete_analytic_spine_l2_r2_progress_index_surface_ready <|
    And.intro concrete_l2_diagonal_raw_action_unit_self <|
      And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the concrete `l2` unit probe surface. -/
def concreteAnalyticSpineL2UnitProbeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnitProbeSurfaceReady

/-- Boundary theorem for the concrete `l2` unit probe surface. -/
theorem concrete_analytic_spine_l2_unit_probe_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnitProbeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unit_probe_surface_ready

end

end MathlibAnalytic
end MGAP4D
