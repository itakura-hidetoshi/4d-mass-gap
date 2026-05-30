import Mathlib.Analysis.InnerProductSpace.Continuous
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AdjointContainmentSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

abbrev ConcreteL2R2PairSpace :=
  (lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2)

/-- Coordinate-unit graph point for the completed diagonal graph. -/
theorem concrete_l2_r2_completed_diagonal_unit_graph_mem (n : ℕ) :
    (concreteL2MathlibUnit n,
      concreteL2DiagonalWeight n • concreteL2MathlibUnit n) ∈
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  intro m
  change
    (concreteL2DiagonalWeight n • concreteL2MathlibUnit n) m =
      concreteL2DiagonalWeight m * concreteL2MathlibUnit n m
  by_cases h : m = n
  · subst m
    simp [concrete_l2_mathlib_unit_apply_self]
  · have hunit : concreteL2MathlibUnit n m = 0 := by
      exact concrete_l2_mathlib_unit_apply_ne h
    simp [hunit]

/-- Testing against a Mathlib coordinate unit extracts the corresponding
coordinate. -/
theorem concrete_l2_r2_inner_mathlib_unit_eq_coordinate
    (w : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    inner ℝ w (concreteL2MathlibUnit n) = w n := by
  rw [concrete_l2_r2_inner_eq_coordinate_tsum_pairing]
  unfold concreteL2R2CoordinateTsumPairing
  have hs :
      HasSum
        (fun m : ℕ => w m * concreteL2MathlibUnit n m)
        (w n * concreteL2MathlibUnit n n) := by
    refine hasSum_single n ?_
    intro m hm
    have hunit : concreteL2MathlibUnit n m = 0 := by
      exact concrete_l2_mathlib_unit_apply_ne hm
    simp [hunit]
  have hself : concreteL2MathlibUnit n n = 1 :=
    concrete_l2_mathlib_unit_apply_self n
  calc
    (∑' m : ℕ, w m * concreteL2MathlibUnit n m)
        = w n * concreteL2MathlibUnit n n := hs.tsum_eq
    _ = w n := by
      rw [hself]
      ring

/-- Single-valuedness of the formal adjoint graph candidate: for a fixed input
`y`, the output `w` satisfying all adjoint tests is unique.  The proof tests
against every coordinate-unit graph point and then uses `lp` extensionality. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_single_valued
    {y w₁ w₂ : lp (fun _ : ℕ => ℝ) 2}
    (hw₁ : (y, w₁) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate)
    (hw₂ : (y, w₂) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) :
    w₁ = w₂ := by
  apply concrete_l2_r2_completed_l2_ext
  intro n
  have hgraph := concrete_l2_r2_completed_diagonal_unit_graph_mem n
  have h₁ := hw₁ hgraph
  have h₂ := hw₂ hgraph
  have hinner :
      inner ℝ w₁ (concreteL2MathlibUnit n) =
        inner ℝ w₂ (concreteL2MathlibUnit n) := by
    calc
      inner ℝ w₁ (concreteL2MathlibUnit n)
          = inner ℝ y (concreteL2DiagonalWeight n • concreteL2MathlibUnit n) := h₁
      _ = inner ℝ w₂ (concreteL2MathlibUnit n) := h₂.symm
  simpa [concrete_l2_r2_inner_mathlib_unit_eq_coordinate] using hinner

/-- The formal adjoint graph candidate is closed under addition. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_add
    {p q : ConcreteL2R2PairSpace}
    (hp : p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate)
    (hq : q ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) :
    p + q ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rcases p with ⟨y₁, w₁⟩
  rcases q with ⟨y₂, w₂⟩
  intro z Tz hzgraph
  have hpz := hp hzgraph
  have hqz := hq hzgraph
  change inner ℝ (w₁ + w₂) z = inner ℝ (y₁ + y₂) Tz
  calc
    inner ℝ (w₁ + w₂) z
        = inner ℝ w₁ z + inner ℝ w₂ z := by rw [inner_add_left]
    _ = inner ℝ y₁ Tz + inner ℝ y₂ Tz := by rw [hpz, hqz]
    _ = inner ℝ (y₁ + y₂) Tz := by rw [inner_add_left]

/-- The formal adjoint graph candidate is closed under scalar multiplication. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_smul
    (c : ℝ) {p : ConcreteL2R2PairSpace}
    (hp : p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) :
    c • p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rcases p with ⟨y, w⟩
  intro z Tz hzgraph
  have hpz := hp hzgraph
  change inner ℝ (c • w) z = inner ℝ (c • y) Tz
  calc
    inner ℝ (c • w) z
        = c * inner ℝ w z := by rw [real_inner_smul_left]
    _ = c * inner ℝ y Tz := by rw [hpz]
    _ = inner ℝ (c • y) Tz := by rw [real_inner_smul_left]

/-- The formal adjoint graph candidate contains zero. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_zero :
    (0 : ConcreteL2R2PairSpace) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  intro z Tz hzgraph
  simp

/-- Linear-structure packet for the formal adjoint graph candidate. -/
def concreteL2R2FormalAdjointGraphCandidateLinear : Prop :=
  (0 : ConcreteL2R2PairSpace) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  (∀ {p q : ConcreteL2R2PairSpace},
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    q ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    p + q ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (∀ (c : ℝ) {p : ConcreteL2R2PairSpace},
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    c • p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate)

/-- The formal adjoint graph candidate is a linear subset of the Hilbert pair
space. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_linear :
    concreteL2R2FormalAdjointGraphCandidateLinear := by
  refine ⟨
    concrete_l2_r2_formal_adjoint_graph_candidate_zero,
    ?_,
    ?_⟩
  · intro p q hp hq
    exact concrete_l2_r2_formal_adjoint_graph_candidate_add (p := p) (q := q) hp hq
  · intro c p hp
    exact concrete_l2_r2_formal_adjoint_graph_candidate_smul c (p := p) hp

/-- Closed-model presentation of the formal adjoint candidate as an intersection
of closed test hyperplanes indexed by graph points. -/
def concreteL2R2CompletedDiagonalFormalAdjointGraphCandidateClosedModel :
    Set ConcreteL2R2PairSpace :=
  ⋂ q : {q : ConcreteL2R2PairSpace //
      q ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier},
    {p : ConcreteL2R2PairSpace |
      inner ℝ p.2 q.1.1 = inner ℝ p.1 q.1.2}

/-- The closed-model presentation is exactly the original formal adjoint graph
candidate. -/
theorem concrete_l2_r2_formal_adjoint_closed_model_eq_candidate :
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidateClosedModel =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  ext p
  constructor
  · intro hp
    intro z Tz hzgraph
    have htest := Set.mem_iInter.mp hp ⟨(z, Tz), hzgraph⟩
    exact htest
  · intro hp
    apply Set.mem_iInter.mpr
    intro q
    rcases q with ⟨⟨z, Tz⟩, hzgraph⟩
    exact hp hzgraph

/-- Each adjoint-test hyperplane in the closed-model presentation is closed. -/
theorem concrete_l2_r2_formal_adjoint_test_hyperplane_isClosed
    (q : {q : ConcreteL2R2PairSpace //
      q ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier}) :
    IsClosed
      {p : ConcreteL2R2PairSpace |
        inner ℝ p.2 q.1.1 = inner ℝ p.1 q.1.2} := by
  exact isClosed_eq (continuous_snd.inner continuous_const)
    (continuous_fst.inner continuous_const)

/-- The formal adjoint graph candidate is closed as an intersection of closed
adjoint-test hyperplanes. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_isClosed :
    IsClosed concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rw [← concrete_l2_r2_formal_adjoint_closed_model_eq_candidate]
  unfold concreteL2R2CompletedDiagonalFormalAdjointGraphCandidateClosedModel
  apply isClosed_iInter
  intro q
  exact concrete_l2_r2_formal_adjoint_test_hyperplane_isClosed q

/-- Structure surface bundling single-valuedness, linearity, and closedness for
the formal adjoint graph candidate. -/
structure ConcreteL2R2AdjointGraphCandidateStructureSurface where
  adjointContainmentSurfaceReady : concreteAnalyticSpineL2R2AdjointContainmentSurfaceReady
  formalAdjointSingleValued :
    ∀ {y w₁ w₂ : lp (fun _ : ℕ => ℝ) 2},
      (y, w₁) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
      (y, w₂) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
      w₁ = w₂
  formalAdjointLinear : concreteL2R2FormalAdjointGraphCandidateLinear
  formalAdjointClosed : IsClosed concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate
  boundaryNotReverseAdjointContainment : Prop
  boundaryNotAdjointDomainAgreementTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop

/-- Concrete structure surface for the formal adjoint graph candidate. -/
def concreteL2R2AdjointGraphCandidateStructureSurface :
    ConcreteL2R2AdjointGraphCandidateStructureSurface :=
  { adjointContainmentSurfaceReady :=
      concrete_analytic_spine_l2_r2_adjoint_containment_surface_ready
    formalAdjointSingleValued := by
      intro y w₁ w₂ hw₁ hw₂
      exact concrete_l2_r2_formal_adjoint_graph_candidate_single_valued hw₁ hw₂
    formalAdjointLinear :=
      concrete_l2_r2_formal_adjoint_graph_candidate_linear
    formalAdjointClosed :=
      concrete_l2_r2_formal_adjoint_graph_candidate_isClosed
    boundaryNotReverseAdjointContainment := True
    boundaryNotAdjointDomainAgreementTheorem := True
    boundaryNotSelfAdjointnessTheorem := True }

/-- Public readiness predicate for the formal adjoint graph candidate structure. -/
def concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2AdjointContainmentSurfaceReady ∧
  (∀ {y w₁ w₂ : lp (fun _ : ℕ => ℝ) 2},
    (y, w₁) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    (y, w₂) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    w₁ = w₂) ∧
  concreteL2R2FormalAdjointGraphCandidateLinear ∧
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  True ∧ True ∧ True

/-- The formal adjoint graph candidate structure surface is ready. -/
theorem concrete_analytic_spine_l2_r2_adjoint_graph_candidate_structure_surface_ready :
    concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady := by
  refine ⟨
    concrete_analytic_spine_l2_r2_adjoint_containment_surface_ready,
    ?_,
    concrete_l2_r2_formal_adjoint_graph_candidate_linear,
    concrete_l2_r2_formal_adjoint_graph_candidate_isClosed,
    trivial,
    trivial,
    trivial⟩
  intro y w₁ w₂ hw₁ hw₂
  exact concrete_l2_r2_formal_adjoint_graph_candidate_single_valued hw₁ hw₂

end

end MathlibAnalytic
end MGAP4D
