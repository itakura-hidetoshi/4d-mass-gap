import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrier

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Elements of the bounded-prefix graph-pair carrier.  This is a `Subtype`
interface over the concrete graph-pair space, deliberately kept before any
claim of a completed graph-norm space or closed operator domain. -/
def ConcreteL2GraphPairPrefixEnergyBoundedElement : Type :=
  { p : ConcreteL2GraphPairSpace //
      p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier }

/-- Zero as a bounded-prefix carrier element. -/
def concreteL2GraphPairPrefixEnergyBoundedZero :
    ConcreteL2GraphPairPrefixEnergyBoundedElement :=
  ⟨concreteL2GraphPairZero,
    concrete_l2_graph_pair_prefix_energy_bounded_zero_mem⟩

/-- Addition preserves the bounded-prefix carrier.  This is derived directly
from the finite-prefix additive estimate and mathlib monotonicity of nonnegative
scalar multiplication on `ℝ`. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_mem
    {p q : ConcreteL2GraphPairSpace}
    (hp : p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier)
    (hq : q ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier) :
    concreteL2GraphPairAdd p q ∈
      concreteL2GraphPairPrefixEnergyBoundedCarrier := by
  rcases hp with ⟨Bp, hpB⟩
  rcases hq with ⟨Bq, hqB⟩
  refine ⟨(2 : ℝ) • Bp + (2 : ℝ) • Bq, ?_⟩
  intro N
  exact le_trans
    (concrete_l2_graph_pair_energy_prefix_add_le_prefix_bound N p q)
    (add_le_add
      (smul_le_smul_of_nonneg_left (hpB N) (by norm_num : (0 : ℝ) ≤ 2))
      (smul_le_smul_of_nonneg_left (hqB N) (by norm_num : (0 : ℝ) ≤ 2)))

/-- Scalar multiplication preserves the bounded-prefix carrier. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_mem
    (c : ℝ) {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier) :
    concreteL2GraphPairSmul c p ∈
      concreteL2GraphPairPrefixEnergyBoundedCarrier := by
  rcases hp with ⟨Bp, hpB⟩
  refine ⟨(c ^ 2) • Bp, ?_⟩
  intro N
  rw [concrete_l2_graph_pair_energy_prefix_smul_eq_prefix_smul]
  exact smul_le_smul_of_nonneg_left (hpB N) (sq_nonneg c)

/-- Addition on bounded-prefix carrier elements. -/
def concreteL2GraphPairPrefixEnergyBoundedAdd
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    ConcreteL2GraphPairPrefixEnergyBoundedElement :=
  ⟨concreteL2GraphPairAdd x.1 y.1,
    concrete_l2_graph_pair_prefix_energy_bounded_add_mem x.2 y.2⟩

/-- Scalar multiplication on bounded-prefix carrier elements. -/
def concreteL2GraphPairPrefixEnergyBoundedSmul
    (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    ConcreteL2GraphPairPrefixEnergyBoundedElement :=
  ⟨concreteL2GraphPairSmul c x.1,
    concrete_l2_graph_pair_prefix_energy_bounded_smul_mem c x.2⟩

/-- Coercion law for bounded-prefix carrier addition. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_coe
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    (concreteL2GraphPairPrefixEnergyBoundedAdd x y).1 =
      concreteL2GraphPairAdd x.1 y.1 := by
  rfl

/-- Coercion law for bounded-prefix carrier scalar multiplication. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_coe
    (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    (concreteL2GraphPairPrefixEnergyBoundedSmul c x).1 =
      concreteL2GraphPairSmul c x.1 := by
  rfl

/-- R2ab readiness: the bounded-prefix carrier has an explicit subtype-level
zero/add/smul surface.  This is a clean linear interface, but still only at the
prefix-energy carrier level; it does not assert a completed normed vector space,
closed graph operator, self-adjointness, spectral theorem, PVM, or positive
spectral weight. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrierSurfaceReady ∧
  Nonempty ConcreteL2GraphPairPrefixEnergyBoundedElement ∧
  (∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    q ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    concreteL2GraphPairAdd p q ∈
      concreteL2GraphPairPrefixEnergyBoundedCarrier) ∧
  (∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    concreteL2GraphPairSmul c p ∈
      concreteL2GraphPairPrefixEnergyBoundedCarrier) ∧
  Nonempty
    (ConcreteL2GraphPairPrefixEnergyBoundedElement →
      ConcreteL2GraphPairPrefixEnergyBoundedElement →
      ConcreteL2GraphPairPrefixEnergyBoundedElement) ∧
  Nonempty
    (ℝ → ConcreteL2GraphPairPrefixEnergyBoundedElement →
      ConcreteL2GraphPairPrefixEnergyBoundedElement)

/-- Readiness theorem for R2ab. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_linear_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_carrier_surface_ready <|
      And.intro ⟨concreteL2GraphPairPrefixEnergyBoundedZero⟩ <|
        And.intro
          (fun hp hq =>
            concrete_l2_graph_pair_prefix_energy_bounded_add_mem hp hq) <|
          And.intro
            (fun c hp =>
              concrete_l2_graph_pair_prefix_energy_bounded_smul_mem c hp) <|
            And.intro
              ⟨concreteL2GraphPairPrefixEnergyBoundedAdd⟩
              ⟨concreteL2GraphPairPrefixEnergyBoundedSmul⟩

/-- Boundary marker for R2ab. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearSurfaceReady

/-- Boundary theorem for R2ab. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_linear_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedLinearHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_linear_surface_ready

end

end MathlibAnalytic
end MGAP4D
