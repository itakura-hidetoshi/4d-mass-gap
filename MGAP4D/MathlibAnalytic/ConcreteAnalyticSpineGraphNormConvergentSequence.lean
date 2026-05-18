import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphNormCauchySequence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A graph-norm convergent sequence surface records an explicit real-valued
limit for one concrete graph-norm value sequence.  It is only a sequence-level
limit bookkeeping surface.  It is not a graph-norm completion theorem, not a
Cauchy completion theorem, not a closed-operator theorem, not self-adjointness,
and not an R3 promotion. -/
structure ConcreteGraphNormConvergentSequenceSurface
    (T : ConcreteDenseDomainOperator) where
  graphSequence : ConcreteGraphSequence T
  graphNormLimit : ℝ
  graphNormLimitWitness :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |T.graphNorm (graphSequence.seq n) - graphNormLimit| < ε
  convergentSequenceBoundaryNotCompletionTheorem : Prop

/-- The constant-zero identity graph-norm sequence converges to zero in the
elementary real-valued sense. -/
theorem concrete_identity_graph_norm_sequence_converges_zero :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |concreteIdentityDenseDomainOperator.graphNorm
        (concreteIdentityGraphSequence.seq n) - 0| < ε := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _
  rw [concrete_identity_graph_norm_sequence_zero n]
  simpa using hε

/-- The identity graph sequence has a concrete graph-norm convergence surface.
This does not assert graph-norm completion, Cauchy completion, closedness,
self-adjointness, a spectral theorem, a PVM, or any `33/20` atom. -/
def concreteIdentityGraphNormConvergentSequenceSurface :
    ConcreteGraphNormConvergentSequenceSurface concreteIdentityDenseDomainOperator :=
  { graphSequence := concreteIdentityGraphSequence
    graphNormLimit := 0
    graphNormLimitWitness := concrete_identity_graph_norm_sequence_converges_zero
    convergentSequenceBoundaryNotCompletionTheorem := True }

/-- The graph-norm convergent sequence surface keeps the completion boundary
closed. -/
theorem concrete_identity_graph_norm_convergent_sequence_boundary :
    concreteIdentityGraphNormConvergentSequenceSurface.convergentSequenceBoundaryNotCompletionTheorem := by
  trivial

/-- R2 graph-norm-convergent-sequence readiness for the from-scratch concrete
analytic spine.  This records a concrete zero limit for the toy identity
sequence while staying below graph-norm completion, Cauchy completion,
closed-operator status, and R3. -/
def concreteAnalyticSpineR2GraphNormConvergentSequenceSurfaceReady : Prop :=
  concreteAnalyticSpineR2GraphNormCauchySequenceSurfaceReady ∧
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |concreteIdentityDenseDomainOperator.graphNorm
      (concreteIdentityGraphSequence.seq n) - 0| < ε) ∧
  concreteIdentityGraphNormConvergentSequenceSurface.convergentSequenceBoundaryNotCompletionTheorem

/-- R2 graph-norm-convergent-sequence readiness for the from-scratch concrete
analytic spine. -/
theorem concrete_analytic_spine_r2_graph_norm_convergent_sequence_surface_ready :
    concreteAnalyticSpineR2GraphNormConvergentSequenceSurfaceReady := by
  unfold concreteAnalyticSpineR2GraphNormConvergentSequenceSurfaceReady
  exact And.intro concrete_analytic_spine_r2_graph_norm_cauchy_sequence_surface_ready <|
    And.intro concrete_identity_graph_norm_sequence_converges_zero
      concrete_identity_graph_norm_convergent_sequence_boundary

/-- Boundary marker: the graph-norm convergent sequence surface has not
discharged graph-norm completion, Cauchy completion, the physical nonbounded
Hamiltonian, closedness, self-adjointness, PVM, plaquette observable,
non-definitional `33/20` emergence, or positive spectral-weight derivation. -/
def concreteAnalyticSpineR2GraphNormConvergentSequenceHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineR2GraphNormConvergentSequenceSurfaceReady

/-- Boundary theorem for the R2 graph-norm-convergent-sequence addendum. -/
theorem concrete_analytic_spine_r2_graph_norm_convergent_sequence_hard_residual_boundary_held :
    concreteAnalyticSpineR2GraphNormConvergentSequenceHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_r2_graph_norm_convergent_sequence_surface_ready

end

end MathlibAnalytic
end MGAP4D
