import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphNormBoundedSequence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A graph-norm Cauchy sequence surface records an explicit Cauchy modulus for
one concrete graph-norm value sequence.  It is only a sequence-level Cauchy
bookkeeping surface.  It is not a graph-norm completion theorem, not a Cauchy
completion theorem, not a closed-operator theorem, not self-adjointness, and not
an R3 promotion. -/
structure ConcreteGraphNormCauchySequenceSurface
    (T : ConcreteDenseDomainOperator) where
  graphSequence : ConcreteGraphSequence T
  cauchyModulusWitness :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      |T.graphNorm (graphSequence.seq m) - T.graphNorm (graphSequence.seq n)| < ε
  cauchySequenceBoundaryNotCompletionTheorem : Prop

/-- The constant-zero identity graph-norm sequence is Cauchy in the elementary
real-valued sense. -/
theorem concrete_identity_graph_norm_sequence_cauchy_zero :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      |concreteIdentityDenseDomainOperator.graphNorm
          (concreteIdentityGraphSequence.seq m) -
        concreteIdentityDenseDomainOperator.graphNorm
          (concreteIdentityGraphSequence.seq n)| < ε := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro m n _ _
  rw [concrete_identity_graph_norm_sequence_zero m,
    concrete_identity_graph_norm_sequence_zero n]
  simpa using hε

/-- The identity graph sequence has a concrete graph-norm Cauchy surface.  This
does not assert graph-norm completion, Cauchy completion, closedness,
self-adjointness, a spectral theorem, a PVM, or any `33/20` atom. -/
def concreteIdentityGraphNormCauchySequenceSurface :
    ConcreteGraphNormCauchySequenceSurface concreteIdentityDenseDomainOperator :=
  { graphSequence := concreteIdentityGraphSequence
    cauchyModulusWitness := concrete_identity_graph_norm_sequence_cauchy_zero
    cauchySequenceBoundaryNotCompletionTheorem := True }

/-- The graph-norm Cauchy sequence surface keeps the completion boundary closed. -/
theorem concrete_identity_graph_norm_cauchy_sequence_boundary :
    concreteIdentityGraphNormCauchySequenceSurface.cauchySequenceBoundaryNotCompletionTheorem := by
  trivial

/-- R2 graph-norm-Cauchy-sequence readiness for the from-scratch concrete
analytic spine.  This records a concrete Cauchy modulus for the toy identity
sequence while staying below graph-norm completion, Cauchy completion,
closed-operator status, and R3. -/
def concreteAnalyticSpineR2GraphNormCauchySequenceSurfaceReady : Prop :=
  concreteAnalyticSpineR2GraphNormBoundedSequenceSurfaceReady ∧
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    |concreteIdentityDenseDomainOperator.graphNorm
        (concreteIdentityGraphSequence.seq m) -
      concreteIdentityDenseDomainOperator.graphNorm
        (concreteIdentityGraphSequence.seq n)| < ε) ∧
  concreteIdentityGraphNormCauchySequenceSurface.cauchySequenceBoundaryNotCompletionTheorem

/-- R2 graph-norm-Cauchy-sequence readiness for the from-scratch concrete
analytic spine. -/
theorem concrete_analytic_spine_r2_graph_norm_cauchy_sequence_surface_ready :
    concreteAnalyticSpineR2GraphNormCauchySequenceSurfaceReady := by
  unfold concreteAnalyticSpineR2GraphNormCauchySequenceSurfaceReady
  exact And.intro concrete_analytic_spine_r2_graph_norm_bounded_sequence_surface_ready <|
    And.intro concrete_identity_graph_norm_sequence_cauchy_zero
      concrete_identity_graph_norm_cauchy_sequence_boundary

/-- Boundary marker: the graph-norm Cauchy sequence surface has not discharged
graph-norm completion, Cauchy completion, the physical nonbounded Hamiltonian,
closedness, self-adjointness, PVM, plaquette observable, non-definitional
`33/20` emergence, or positive spectral-weight derivation. -/
def concreteAnalyticSpineR2GraphNormCauchySequenceHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineR2GraphNormCauchySequenceSurfaceReady

/-- Boundary theorem for the R2 graph-norm-Cauchy-sequence addendum. -/
theorem concrete_analytic_spine_r2_graph_norm_cauchy_sequence_hard_residual_boundary_held :
    concreteAnalyticSpineR2GraphNormCauchySequenceHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_r2_graph_norm_cauchy_sequence_surface_ready

end

end MathlibAnalytic
end MGAP4D
