import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AdjointGraphCandidateStructure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Domain of the formal adjoint operator value extracted from the closed,
linear, single-valued formal adjoint graph candidate. -/
def concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate :
    Set (lp (fun _ : ℕ => ℝ) 2) :=
  {y | ∃ w : lp (fun _ : ℕ => ℝ) 2,
    (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate}

/-- The formal adjoint operator value obtained by choosing the unique output from
its graph candidate.  Uniqueness is supplied by
`concrete_l2_r2_formal_adjoint_graph_candidate_single_valued`. -/
def concreteL2R2CompletedDiagonalFormalAdjointOperatorValue
    (y : lp (fun _ : ℕ => ℝ) 2)
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    lp (fun _ : ℕ => ℝ) 2 :=
  Classical.choose (show ∃ w : lp (fun _ : ℕ => ℝ) 2,
    (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate from hy)

/-- The chosen formal adjoint value really lies in the formal adjoint graph
candidate. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_mem
    (y : lp (fun _ : ℕ => ℝ) 2)
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact Classical.choose_spec (show ∃ w : lp (fun _ : ℕ => ℝ) 2,
    (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate from hy)

/-- Any witness in the formal adjoint graph candidate is equal to the chosen
operator value at the same input. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_unique
    {y w : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (hw : (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) :
    w = concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy := by
  exact concrete_l2_r2_formal_adjoint_graph_candidate_single_valued
    hw (concrete_l2_r2_formal_adjoint_operator_value_mem y hy)

/-- The formal adjoint domain contains zero. -/
theorem concrete_l2_r2_formal_adjoint_domain_zero :
    (0 : lp (fun _ : ℕ => ℝ) 2) ∈
      concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate := by
  exact ⟨0, concrete_l2_r2_formal_adjoint_graph_candidate_zero⟩

/-- The formal adjoint domain candidate is closed under addition. -/
theorem concrete_l2_r2_formal_adjoint_domain_add
    {y₁ y₂ : lp (fun _ : ℕ => ℝ) 2}
    (hy₁ : y₁ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (hy₂ : y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    y₁ + y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate := by
  refine ⟨
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
      concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂,
    ?_⟩
  simpa using
    concrete_l2_r2_formal_adjoint_graph_candidate_add
      (p := (y₁, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁))
      (q := (y₂, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂))
      (concrete_l2_r2_formal_adjoint_operator_value_mem y₁ hy₁)
      (concrete_l2_r2_formal_adjoint_operator_value_mem y₂ hy₂)

/-- The formal adjoint domain candidate is closed under scalar multiplication. -/
theorem concrete_l2_r2_formal_adjoint_domain_smul
    (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    c • y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate := by
  refine ⟨c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy, ?_⟩
  simpa using
    concrete_l2_r2_formal_adjoint_graph_candidate_smul c
      (p := (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy))
      (concrete_l2_r2_formal_adjoint_operator_value_mem y hy)

/-- Additivity of the chosen formal adjoint operator value, expressed with the
canonical domain proof for the sum. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_add
    {y₁ y₂ : lp (fun _ : ℕ => ℝ) 2}
    (hy₁ : y₁ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (hy₂ : y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue
        (y₁ + y₂)
        (concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂) =
      concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
        concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂ := by
  exact (concrete_l2_r2_formal_adjoint_operator_value_unique
    (hy := concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂)
    (hw := by
      simpa using
        concrete_l2_r2_formal_adjoint_graph_candidate_add
          (p := (y₁, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁))
          (q := (y₂, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂))
          (concrete_l2_r2_formal_adjoint_operator_value_mem y₁ hy₁)
          (concrete_l2_r2_formal_adjoint_operator_value_mem y₂ hy₂))).symm

/-- Homogeneity of the chosen formal adjoint operator value, expressed with the
canonical domain proof for the scalar multiple. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_smul
    (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue
        (c • y)
        (concrete_l2_r2_formal_adjoint_domain_smul c hy) =
      c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy := by
  exact (concrete_l2_r2_formal_adjoint_operator_value_unique
    (hy := concrete_l2_r2_formal_adjoint_domain_smul c hy)
    (hw := by
      simpa using
        concrete_l2_r2_formal_adjoint_graph_candidate_smul c
          (p := (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy))
          (concrete_l2_r2_formal_adjoint_operator_value_mem y hy))).symm

/-- Coordinate equation extracted from a formal adjoint graph candidate witness.
This is the key reverse-containment equation: testing against the `n`-th
coordinate-unit graph point forces `w n = λₙ y n`. -/
theorem concrete_l2_r2_formal_adjoint_candidate_coordinate_equation
    {y w : lp (fun _ : ℕ => ℝ) 2}
    (hw : (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate)
    (n : ℕ) :
    w n = concreteL2DiagonalWeight n * y n := by
  have hgraph := concrete_l2_r2_completed_diagonal_unit_graph_mem n
  have htest := hw hgraph
  have hleft : inner ℝ w (concreteL2MathlibUnit n) = w n :=
    concrete_l2_r2_inner_mathlib_unit_eq_coordinate w n
  have hright :
      inner ℝ y (concreteL2DiagonalWeight n • concreteL2MathlibUnit n) =
        concreteL2DiagonalWeight n * y n := by
    calc
      inner ℝ y (concreteL2DiagonalWeight n • concreteL2MathlibUnit n)
          = concreteL2DiagonalWeight n * inner ℝ y (concreteL2MathlibUnit n) := by
            rw [real_inner_smul_right]
      _ = concreteL2DiagonalWeight n * y n := by
            rw [concrete_l2_r2_inner_mathlib_unit_eq_coordinate y n]
  calc
    w n = inner ℝ w (concreteL2MathlibUnit n) := hleft.symm
    _ = inner ℝ y (concreteL2DiagonalWeight n • concreteL2MathlibUnit n) := htest
    _ = concreteL2DiagonalWeight n * y n := hright

/-- Coordinate equation for the chosen formal adjoint operator value. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation
    (y : lp (fun _ : ℕ => ℝ) 2)
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (n : ℕ) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy n =
      concreteL2DiagonalWeight n * y n := by
  exact concrete_l2_r2_formal_adjoint_candidate_coordinate_equation
    (concrete_l2_r2_formal_adjoint_operator_value_mem y hy) n

/-- The chosen formal adjoint operator value satisfies the original completed
operator graph equation. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_graph_mem
    (y : lp (fun _ : ℕ => ℝ) 2)
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  intro n
  exact concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation y hy n

/-- Reverse containment of the formal adjoint graph candidate into the original
completed diagonal graph.  This is not yet a Mathlib `IsSelfAdjoint` theorem; it
is the graph-level reverse-containment theorem produced by coordinate extraction. -/
theorem concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph :
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  intro p hp
  rcases p with ⟨y, w⟩
  have hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate := ⟨w, hp⟩
  have hvalue : w = concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy :=
    concrete_l2_r2_formal_adjoint_operator_value_unique hy hp
  rw [hvalue]
  exact concrete_l2_r2_formal_adjoint_operator_value_graph_mem y hy

/-- Graph-level equality between the completed diagonal graph and its formal
adjoint graph candidate. -/
theorem concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  apply Set.Subset.antisymm
  · exact concrete_l2_r2_completed_diagonal_graph_subset_formal_adjoint_candidate
  · exact concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph

/-- Surface bundling the formal adjoint operator value and the coordinate-equation
reverse containment extracted from the closed, linear, single-valued candidate. -/
structure ConcreteL2R2FormalAdjointOperatorValueSurface where
  candidateStructureSurfaceReady : concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady
  domainZero :
    (0 : lp (fun _ : ℕ => ℝ) 2) ∈
      concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate
  domainAdd :
    ∀ {y₁ y₂ : lp (fun _ : ℕ => ℝ) 2},
      y₁ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
      y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
      y₁ + y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate
  domainSmul :
    ∀ (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2},
      y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
      c • y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate
  operatorValueCoordinateEquation :
    ∀ (y : lp (fun _ : ℕ => ℝ) 2)
      (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
      (n : ℕ),
      concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy n =
        concreteL2DiagonalWeight n * y n
  graphReverseContainment :
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier
  graphCandidateEquality :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate
  boundaryNotMathlibAdjointIdentifier : Prop
  boundaryNotSelfAdjointnessTheorem : Prop

/-- Concrete formal adjoint operator value surface. -/
def concreteL2R2FormalAdjointOperatorValueSurface :
    ConcreteL2R2FormalAdjointOperatorValueSurface :=
  { candidateStructureSurfaceReady :=
      concrete_analytic_spine_l2_r2_adjoint_graph_candidate_structure_surface_ready
    domainZero := concrete_l2_r2_formal_adjoint_domain_zero
    domainAdd := by
      intro y₁ y₂ hy₁ hy₂
      exact concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂
    domainSmul := by
      intro c y hy
      exact concrete_l2_r2_formal_adjoint_domain_smul c hy
    operatorValueCoordinateEquation := by
      intro y hy n
      exact concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation y hy n
    graphReverseContainment :=
      concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph
    graphCandidateEquality :=
      concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate
    boundaryNotMathlibAdjointIdentifier := True
    boundaryNotSelfAdjointnessTheorem := True }

/-- Public readiness predicate for the formal adjoint operator value and
coordinate-extraction surface. -/
def concreteAnalyticSpineL2R2FormalAdjointOperatorValueSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady ∧
  (0 : lp (fun _ : ℕ => ℝ) 2) ∈
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate ∧
  (∀ {y₁ y₂ : lp (fun _ : ℕ => ℝ) 2},
    y₁ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
    y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
    y₁ + y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2},
    y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
    c • y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ (y : lp (fun _ : ℕ => ℝ) 2)
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (n : ℕ),
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy n =
      concreteL2DiagonalWeight n * y n) ∧
  concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  True ∧ True

/-- The formal adjoint operator value and coordinate-extraction surface is ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_operator_value_surface_ready :
    concreteAnalyticSpineL2R2FormalAdjointOperatorValueSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_adjoint_graph_candidate_structure_surface_ready,
    concrete_l2_r2_formal_adjoint_domain_zero,
    fun hy₁ hy₂ => concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂,
    fun c hy => concrete_l2_r2_formal_adjoint_domain_smul c hy,
    fun y hy n => concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation y hy n,
    concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph,
    concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
