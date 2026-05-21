import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedSeminormCandidate

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Square identity behind absolute homogeneity of the bounded finite-prefix
seminorm candidate.  This lemma keeps the algebra at square level and uses
mathlib's `sq_abs`, `ring`, and the already-proved square-recovery theorem. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs_sq
    (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) ^ 2 =
      (|c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ^ 2 := by
  have hleft :
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
          (concreteL2GraphPairPrefixEnergyBoundedSmul c x) ^ 2 =
        (c ^ 2) * concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
    rw [concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq]
    rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq]
    simp [smul_eq_mul]
  have hright :
      (|c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ^ 2 =
        (c ^ 2) * concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
    calc
      (|c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ^ 2
          = |c| ^ 2 * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x ^ 2 := by
        ring
      _ = c ^ 2 * concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
        rw [sq_abs]
        rw [concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq]
  exact hleft.trans hright.symm

/-- Absolute homogeneity for the bounded finite-prefix seminorm candidate.
The proof uses a standard mathlib square-equality split, then rules out the
negative branch by nonnegativity of both sides. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs
    (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      |c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x := by
  have hsquares :=
    concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs_sq N c x
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquares) with h | h
  · exact h
  · have hleft_nonneg :
        0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
          (concreteL2GraphPairPrefixEnergyBoundedSmul c x) :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
    have hright_nonneg :
        0 ≤ |c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x :=
      mul_nonneg (abs_nonneg c)
        (concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg N x)
    nlinarith

/-- R2af bounded finite-prefix absolute-homogeneity adapter surface.  This is
still below a full seminorm instance: it provides nonnegativity, zero, square
recovery, and absolute homogeneity, but keeps triangle inequality and the
normed-space/topological/spectral boundaries closed. -/
structure ConcreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface where
  r2aeReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedSeminormCandidateReady
  seminormCandidate : ℕ → ConcreteL2GraphPairPrefixEnergyBoundedElement → ℝ
  seminormCandidateNonneg : ∀ (N : ℕ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ seminormCandidate N x
  seminormCandidateZero : ∀ N : ℕ,
    seminormCandidate N concreteL2GraphPairPrefixEnergyBoundedZero = 0
  seminormCandidateSq : ∀ (N : ℕ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    seminormCandidate N x ^ 2 =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x
  seminormCandidateSmulAbsSq : ∀ (N : ℕ) (c : ℝ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    seminormCandidate N (concreteL2GraphPairPrefixEnergyBoundedSmul c x) ^ 2 =
      (|c| * seminormCandidate N x) ^ 2
  seminormCandidateSmulAbs : ∀ (N : ℕ) (c : ℝ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    seminormCandidate N (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      |c| * seminormCandidate N x
  boundaryNotTriangleInequality : Prop
  boundaryNotSeminormInstance : Prop
  boundaryNotNormedSpaceInstance : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2af bounded finite-prefix absolute-homogeneity surface. -/
def concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface :
    ConcreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface :=
  { r2aeReady :=
      concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_seminorm_candidate_ready
    seminormCandidate := concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
    seminormCandidateNonneg :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg
    seminormCandidateZero :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_zero
    seminormCandidateSq :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq
    seminormCandidateSmulAbsSq :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs_sq
    seminormCandidateSmulAbs :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs
    boundaryNotTriangleInequality := True
    boundaryNotSeminormInstance := True
    boundaryNotNormedSpaceInstance := True
    boundaryNotGraphNormTopology := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2af readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedSeminormCandidateReady ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    0 ≤ concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ∧
  (∀ N : ℕ,
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
      concreteL2GraphPairPrefixEnergyBoundedZero = 0) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x ^ 2 =
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) ∧
  (∀ (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) ^ 2 =
      (|c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ^ 2) ∧
  (∀ (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) =
      |c| * concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotTriangleInequality ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotSeminormInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotNormedSpaceInstance ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneitySurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2af. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_absolute_homogeneity_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_seminorm_candidate_ready <|
      And.intro
        concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_nonneg <|
        And.intro
          concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_zero <|
          And.intro
            concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq <|
            And.intro
              concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs_sq <|
              And.intro
                concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs <|
                And.intro trivial <| And.intro trivial <| And.intro trivial <|
                  And.intro trivial <| And.intro trivial <| And.intro trivial <|
                    And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2af. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityReady

/-- Boundary theorem for R2af. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_absolute_homogeneity_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedAbsoluteHomogeneityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_absolute_homogeneity_ready

end

end MathlibAnalytic
end MGAP4D
