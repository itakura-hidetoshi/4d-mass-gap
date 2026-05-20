import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalGraphLinearClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The explicit graph-pair zero is the same zero point already known to lie in
the diagonal `l2` graph carrier. -/
theorem concrete_l2_diagonal_graph_l2_pair_zero_mem :
    concreteL2GraphPairZero ∈ ConcreteL2DiagonalGraphL2Carrier := by
  simpa [concreteL2GraphPairZero] using
    concrete_l2_diagonal_zero_graph_l2_point_mem

/-- The diagonal `l2` graph carrier contains the explicit zero pair and is closed
under the explicit graph-pair addition and scalar multiplication introduced in
R2i/R2j.  This is an explicit linear-substructure surface, not a mathlib
`Submodule` instance. -/
structure ConcreteL2R2DiagonalGraphLinearSubstructureSurface where
  r2jReady : concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady
  carrier : Set ConcreteL2GraphPairSpace
  zeroMem : concreteL2GraphPairZero ∈ carrier
  addClosure : ∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ carrier → q ∈ carrier → concreteL2GraphPairAdd p q ∈ carrier
  smulClosure : ∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ carrier → concreteL2GraphPairSmul c p ∈ carrier
  explicitZero : carrier = ConcreteL2DiagonalGraphL2Carrier →
    concreteL2GraphPairZero ∈ ConcreteL2DiagonalGraphL2Carrier
  explicitAddClosure : carrier = ConcreteL2DiagonalGraphL2Carrier →
    ∀ {p q : ConcreteL2GraphPairSpace},
      p ∈ ConcreteL2DiagonalGraphL2Carrier →
        q ∈ ConcreteL2DiagonalGraphL2Carrier →
          concreteL2GraphPairAdd p q ∈ ConcreteL2DiagonalGraphL2Carrier
  explicitSmulClosure : carrier = ConcreteL2DiagonalGraphL2Carrier →
    ∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
      p ∈ ConcreteL2DiagonalGraphL2Carrier →
        concreteL2GraphPairSmul c p ∈ ConcreteL2DiagonalGraphL2Carrier
  boundaryNotMathlibSubmoduleInstance : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- The concrete R2k explicit linear-substructure surface. -/
def concreteL2R2DiagonalGraphLinearSubstructureSurface :
    ConcreteL2R2DiagonalGraphLinearSubstructureSurface :=
  { r2jReady :=
      concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_surface_ready
    carrier := ConcreteL2DiagonalGraphL2Carrier
    zeroMem := concrete_l2_diagonal_graph_l2_pair_zero_mem
    addClosure := fun hp hq => concrete_l2_diagonal_graph_l2_add_mem hp hq
    smulClosure := fun c {p} hp => concrete_l2_diagonal_graph_l2_smul_mem c hp
    explicitZero := fun _ => concrete_l2_diagonal_graph_l2_pair_zero_mem
    explicitAddClosure := fun _ hp hq =>
      concrete_l2_diagonal_graph_l2_add_mem hp hq
    explicitSmulClosure := fun _ c {p} hp =>
      concrete_l2_diagonal_graph_l2_smul_mem c hp
    boundaryNotMathlibSubmoduleInstance := True
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2k readiness: the diagonal graph has explicit zero/add/smul closure under
our concrete graph-pair operations. -/
def concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady ∧
  concreteL2GraphPairZero ∈ ConcreteL2DiagonalGraphL2Carrier ∧
  (∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      q ∈ ConcreteL2DiagonalGraphL2Carrier →
        concreteL2GraphPairAdd p q ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  (∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      concreteL2GraphPairSmul c p ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotMathlibSubmoduleInstance ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotPVMConstruction ∧
  concreteL2R2DiagonalGraphLinearSubstructureSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2k. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_linear_substructure_surface_ready :
    concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurfaceReady := by
  unfold concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_surface_ready <|
      And.intro concrete_l2_diagonal_graph_l2_pair_zero_mem <|
        And.intro (fun hp hq => concrete_l2_diagonal_graph_l2_add_mem hp hq) <|
          And.intro (fun c {p} hp => concrete_l2_diagonal_graph_l2_smul_mem c hp) <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial trivial

/-- Boundary marker for R2k. -/
def concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureSurfaceReady

/-- Boundary theorem for R2k. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_linear_substructure_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DiagonalGraphLinearSubstructureHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_diagonal_graph_linear_substructure_surface_ready

end

end MathlibAnalytic
end MGAP4D
