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
its graph candidate. -/
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
  have h₁ :
      (y₁, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y₁ hy₁
  have h₂ :
      (y₂, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y₂ hy₂
  change
    ∀ {z Tz : lp (fun _ : ℕ => ℝ) 2},
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
        inner ℝ
            (concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
              concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂) z =
          inner ℝ (y₁ + y₂) Tz
  intro z Tz hzgraph
  exact (concrete_l2_r2_formal_adjoint_graph_candidate_add
    (p := (y₁, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁))
    (q := (y₂, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂))
    h₁ h₂) (z := z) (Tz := Tz) hzgraph

/-- The formal adjoint domain candidate is closed under scalar multiplication. -/
theorem concrete_l2_r2_formal_adjoint_domain_smul
    (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    c • y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate := by
  refine ⟨c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy, ?_⟩
  have h :
      (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y hy
  change
    ∀ {z Tz : lp (fun _ : ℕ => ℝ) 2},
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
        inner ℝ (c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) z =
          inner ℝ (c • y) Tz
  intro z Tz hzgraph
  exact (concrete_l2_r2_formal_adjoint_graph_candidate_smul c
    (p := (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy)) h)
    (z := z) (Tz := Tz) hzgraph

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
  have h₁ :
      (y₁, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y₁ hy₁
  have h₂ :
      (y₂, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y₂ hy₂
  have hwsum :
      (y₁ + y₂,
        concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
          concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    change
      ∀ {z Tz : lp (fun _ : ℕ => ℝ) 2},
        (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
          inner ℝ
              (concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
                concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂) z =
            inner ℝ (y₁ + y₂) Tz
    intro z Tz hzgraph
    exact (concrete_l2_r2_formal_adjoint_graph_candidate_add
      (p := (y₁, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁))
      (q := (y₂, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂))
      h₁ h₂) (z := z) (Tz := Tz) hzgraph
  exact (concrete_l2_r2_formal_adjoint_operator_value_unique
    (hy := concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂)
    (hw := hwsum)).symm

/-- Homogeneity of the chosen formal adjoint operator value, expressed with the
canonical domain proof for the scalar multiple. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_smul
    (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue
        (c • y)
        (concrete_l2_r2_formal_adjoint_domain_smul c hy) =
      c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy := by
  have h :
      (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y hy
  have hwsmul :
      (c • y, c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    change
      ∀ {z Tz : lp (fun _ : ℕ => ℝ) 2},
        (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
          inner ℝ (c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) z =
            inner ℝ (c • y) Tz
    intro z Tz hzgraph
    exact (concrete_l2_r2_formal_adjoint_graph_candidate_smul c
      (p := (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy)) h)
      (z := z) (Tz := Tz) hzgraph
  exact (concrete_l2_r2_formal_adjoint_operator_value_unique
    (hy := concrete_l2_r2_formal_adjoint_domain_smul c hy)
    (hw := hwsmul)).symm

/-- Coordinate equation extracted from a formal adjoint graph candidate witness.
Testing against the `n`-th coordinate-unit graph point forces
`w n = λₙ * y n`. -/
theorem concrete_l2_r2_formal_adjoint_candidate_coordinate_equation
    {y w : lp (fun _ : ℕ => ℝ) 2}
    (hw : (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate)
    (n : ℕ) :
    w n = concreteL2DiagonalWeight n * y n := by
  have hgraph := concrete_l2_r2_completed_diagonal_unit_graph_mem n
  have htest := hw hgraph
  have hwcoord := concrete_l2_r2_inner_mathlib_unit_eq_coordinate w n
  have hycoord := concrete_l2_r2_inner_mathlib_unit_eq_coordinate y n
  calc
    w n = inner ℝ w (concreteL2MathlibUnit n) := hwcoord.symm
    _ = inner ℝ y (concreteL2DiagonalWeight n • concreteL2MathlibUnit n) := htest
    _ = concreteL2DiagonalWeight n * inner ℝ y (concreteL2MathlibUnit n) := by
        rw [real_inner_smul_right]
    _ = concreteL2DiagonalWeight n * y n := by
        rw [hycoord]

/-- Coordinate equation for the chosen formal adjoint operator value. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation
    {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (n : ℕ) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy n =
      concreteL2DiagonalWeight n * y n := by
  exact concrete_l2_r2_formal_adjoint_candidate_coordinate_equation
    (concrete_l2_r2_formal_adjoint_operator_value_mem y hy) n

/-- Public theorem-entry predicate for the formal adjoint operator-value surface. -/
def concreteAnalyticSpineL2R2FormalAdjointOperatorValueSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady ∧
  ((0 : lp (fun _ : ℕ => ℝ) 2) ∈
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ {y₁ y₂ : lp (fun _ : ℕ => ℝ) 2},
    y₁ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
    y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
    y₁ + y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2},
    y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate →
    c • y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (n : ℕ),
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy n =
      concreteL2DiagonalWeight n * y n)

/-- The formal adjoint operator-value surface is ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_operator_value_surface_ready :
    concreteAnalyticSpineL2R2FormalAdjointOperatorValueSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_adjoint_graph_candidate_structure_surface_ready,
    concrete_l2_r2_formal_adjoint_domain_zero,
    (by intro y₁ y₂ hy₁ hy₂; exact concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂),
    (by intro c y hy; exact concrete_l2_r2_formal_adjoint_domain_smul c hy),
    (by intro y hy n; exact concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation hy n)⟩

end

end MathlibAnalytic
end MGAP4D
