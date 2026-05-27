import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairLinearScaffold

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Diagonal-domain closure under explicit concrete `l2` addition. -/
theorem concrete_l2_diagonal_domain_add_mem
    (x y : ConcreteL2DiagonalDomainCarrier) :
    ConcreteL2DiagonalDomain (concreteL2RealAdd x.1 y.1) := by
  unfold ConcreteL2DiagonalDomain concreteL2RealAdd
  have hsumBound :
      Summable fun n : ℕ =>
        (2 : ℝ) • ((concreteL2DiagonalWeight n)^2 * (x.1.1 n)^2) +
          (2 : ℝ) • ((concreteL2DiagonalWeight n)^2 * (y.1.1 n)^2) := by
    exact (x.2.const_smul (2 : ℝ)).add (y.2.const_smul (2 : ℝ))
  refine Summable.of_nonneg_of_le ?hNonneg ?hLe hsumBound
  · intro n
    exact mul_nonneg (sq_nonneg (concreteL2DiagonalWeight n))
      (sq_nonneg (x.1.1 n + y.1.1 n))
  · intro n
    have hsq := concrete_l2_r2_sq_add_le_two_sq_add_two_sq (x.1.1 n) (y.1.1 n)
    have hw : 0 ≤ (concreteL2DiagonalWeight n)^2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hsq hw
    simpa [two_smul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Concrete diagonal-domain addition. -/
def concreteL2DiagonalDomainAdd
    (x y : ConcreteL2DiagonalDomainCarrier) : ConcreteL2DiagonalDomainCarrier :=
  ⟨concreteL2RealAdd x.1 y.1, concrete_l2_diagonal_domain_add_mem x y⟩

/-- Diagonal-domain closure under explicit concrete scalar multiplication. -/
theorem concrete_l2_diagonal_domain_smul_mem
    (c : ℝ) (x : ConcreteL2DiagonalDomainCarrier) :
    ConcreteL2DiagonalDomain (concreteL2RealSmul c x.1) := by
  unfold ConcreteL2DiagonalDomain concreteL2RealSmul
  have hseq :
      (fun n : ℕ =>
        (concreteL2DiagonalWeight n)^2 * (c * x.1.1 n)^2) =
        (fun n : ℕ => (c ^ 2) •
          ((concreteL2DiagonalWeight n)^2 * (x.1.1 n)^2)) := by
    funext n
    simp [pow_two]
    ring
  rw [hseq]
  exact x.2.const_smul (c ^ 2)

/-- Concrete diagonal-domain scalar multiplication. -/
def concreteL2DiagonalDomainSmul
    (c : ℝ) (x : ConcreteL2DiagonalDomainCarrier) : ConcreteL2DiagonalDomainCarrier :=
  ⟨concreteL2RealSmul c x.1, concrete_l2_diagonal_domain_smul_mem c x⟩

/-- The `l2` diagonal action is compatible with explicit domain addition. -/
theorem concrete_l2_diagonal_action_l2_add_ext
    (x y : ConcreteL2DiagonalDomainCarrier) (n : ℕ) :
    (concreteL2DiagonalActionL2 (concreteL2DiagonalDomainAdd x y)).1 n =
      (concreteL2RealAdd (concreteL2DiagonalActionL2 x)
        (concreteL2DiagonalActionL2 y)).1 n := by
  simp [concreteL2DiagonalActionL2, concreteL2DiagonalDomainAdd,
    concreteL2DiagonalRawAction, concreteL2RealAdd]
  ring

/-- The `l2` diagonal action is compatible with explicit domain scalar
multiplication. -/
theorem concrete_l2_diagonal_action_l2_smul_ext
    (c : ℝ) (x : ConcreteL2DiagonalDomainCarrier) (n : ℕ) :
    (concreteL2DiagonalActionL2 (concreteL2DiagonalDomainSmul c x)).1 n =
      (concreteL2RealSmul c (concreteL2DiagonalActionL2 x)).1 n := by
  simp [concreteL2DiagonalActionL2, concreteL2DiagonalDomainSmul,
    concreteL2DiagonalRawAction, concreteL2RealSmul]
  ring

/-- Pair equality for graph addition. -/
theorem concrete_l2_diagonal_graph_pair_add_eq
    (x y : ConcreteL2DiagonalDomainCarrier) :
    concreteL2GraphPairAdd
      (x.1, concreteL2DiagonalActionL2 x)
      (y.1, concreteL2DiagonalActionL2 y) =
        ((concreteL2DiagonalDomainAdd x y).1,
          concreteL2DiagonalActionL2 (concreteL2DiagonalDomainAdd x y)) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext n
    exact (concrete_l2_diagonal_action_l2_add_ext x y n).symm

/-- Pair equality for graph scalar multiplication. -/
theorem concrete_l2_diagonal_graph_pair_smul_eq
    (c : ℝ) (x : ConcreteL2DiagonalDomainCarrier) :
    concreteL2GraphPairSmul c (x.1, concreteL2DiagonalActionL2 x) =
      ((concreteL2DiagonalDomainSmul c x).1,
        concreteL2DiagonalActionL2 (concreteL2DiagonalDomainSmul c x)) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext n
    exact (concrete_l2_diagonal_action_l2_smul_ext c x n).symm

/-- The diagonal `l2` graph carrier is closed under explicit graph-pair addition. -/
theorem concrete_l2_diagonal_graph_l2_add_mem
    {p q : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2DiagonalGraphL2Carrier)
    (hq : q ∈ ConcreteL2DiagonalGraphL2Carrier) :
    concreteL2GraphPairAdd p q ∈ ConcreteL2DiagonalGraphL2Carrier := by
  rcases hp with ⟨x, rfl⟩
  rcases hq with ⟨y, rfl⟩
  refine ⟨concreteL2DiagonalDomainAdd x y, ?_⟩
  exact concrete_l2_diagonal_graph_pair_add_eq x y

/-- The diagonal `l2` graph carrier is closed under explicit graph-pair scalar
multiplication. -/
theorem concrete_l2_diagonal_graph_l2_smul_mem
    (c : ℝ) {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2DiagonalGraphL2Carrier) :
    concreteL2GraphPairSmul c p ∈ ConcreteL2DiagonalGraphL2Carrier := by
  rcases hp with ⟨x, rfl⟩
  refine ⟨concreteL2DiagonalDomainSmul c x, ?_⟩
  exact concrete_l2_diagonal_graph_pair_smul_eq c x

/-- R2j diagonal graph linear-closure surface. -/
structure ConcreteL2R2DiagonalGraphLinearClosureSurface where
  r2iReady : concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady
  diagonalDomainAddClosure : ∀ x y : ConcreteL2DiagonalDomainCarrier,
    ConcreteL2DiagonalDomain (concreteL2RealAdd x.1 y.1)
  diagonalDomainSmulClosure : ∀ (c : ℝ) (x : ConcreteL2DiagonalDomainCarrier),
    ConcreteL2DiagonalDomain (concreteL2RealSmul c x.1)
  diagonalGraphAddClosure : ∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      q ∈ ConcreteL2DiagonalGraphL2Carrier →
        concreteL2GraphPairAdd p q ∈ ConcreteL2DiagonalGraphL2Carrier
  diagonalGraphSmulClosure : ∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      concreteL2GraphPairSmul c p ∈ ConcreteL2DiagonalGraphL2Carrier
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2j diagonal graph linear-closure surface. -/
def concreteL2R2DiagonalGraphLinearClosureSurface :
    ConcreteL2R2DiagonalGraphLinearClosureSurface :=
  { r2iReady := concrete_analytic_spine_l2_r2_graph_pair_linear_scaffold_ready
    diagonalDomainAddClosure := concrete_l2_diagonal_domain_add_mem
    diagonalDomainSmulClosure := concrete_l2_diagonal_domain_smul_mem
    diagonalGraphAddClosure := fun hp hq =>
      concrete_l2_diagonal_graph_l2_add_mem hp hq
    diagonalGraphSmulClosure := fun c {p} hp =>
      concrete_l2_diagonal_graph_l2_smul_mem c hp
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2j readiness. -/
def concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady ∧
  (∀ x y : ConcreteL2DiagonalDomainCarrier,
    ConcreteL2DiagonalDomain (concreteL2RealAdd x.1 y.1)) ∧
  (∀ (c : ℝ) (x : ConcreteL2DiagonalDomainCarrier),
    ConcreteL2DiagonalDomain (concreteL2RealSmul c x.1)) ∧
  (∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      q ∈ ConcreteL2DiagonalGraphL2Carrier →
        concreteL2GraphPairAdd p q ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  (∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      concreteL2GraphPairSmul c p ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True

/-- Readiness theorem for R2j. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_surface_ready :
    concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady := by
  unfold concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_linear_scaffold_ready <|
      And.intro concrete_l2_diagonal_domain_add_mem <|
        And.intro concrete_l2_diagonal_domain_smul_mem <|
          And.intro (fun hp hq => concrete_l2_diagonal_graph_l2_add_mem hp hq) <|
            And.intro (fun c {p} hp => concrete_l2_diagonal_graph_l2_smul_mem c hp) <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2j. -/
def concreteAnalyticSpineL2R2DiagonalGraphLinearClosureHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady

/-- Boundary theorem for R2j. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DiagonalGraphLinearClosureHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_surface_ready

end

end MathlibAnalytic
end MGAP4D
