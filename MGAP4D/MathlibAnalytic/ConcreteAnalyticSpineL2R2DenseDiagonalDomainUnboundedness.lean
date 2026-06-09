import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMap
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateEvaluationContinuity

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The canonical coordinate-unit probe, now viewed as an element of the promoted
R2 dense diagonal-domain carrier. -/
def concreteL2R2DenseDiagonalDomainUnitProbe
    (k : ℕ) : concreteL2R2DenseDiagonalDomainCarrier :=
  ⟨concreteL2MathlibUnit k, by
    rw [concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq]
    exact concrete_l2_r2_diagonal_domain_candidate_mathlib_unit k⟩

/-- The dense-domain unit probe has ambient Hilbert norm one. -/
theorem concrete_l2_r2_dense_diagonal_domain_unit_probe_norm_eq_one
    (k : ℕ) :
    ‖(concreteL2R2DenseDiagonalDomainUnitProbe k : ConcreteL2R1HilbertCarrier)‖ = 1 := by
  simpa [concreteL2R2DenseDiagonalDomainUnitProbe] using
    concrete_l2_mathlib_unit_norm_eq_one k

/-- At its selected coordinate, the R2 dense-domain diagonal action multiplies the
unit probe by the diagonal weight `(k+1)`. -/
theorem concrete_l2_r2_dense_diagonal_domain_unit_probe_action_coord_self
    (k : ℕ) :
    concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDiagonalDomainUnitProbe k) k =
      concreteL2R2DiagonalWeight k := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord]
  simp [concreteL2R2DenseDiagonalDomainUnitProbe,
    concreteL2R2DenseDiagonalDomainCarrierVal,
    concreteL2R2WeightedCoordinate,
    concreteL2R2DiagonalWeight,
    concrete_l2_mathlib_unit_apply_self]

/-- The R2 diagonal weight is nonnegative. -/
theorem concrete_l2_r2_diagonal_weight_nonneg (k : ℕ) :
    0 ≤ concreteL2R2DiagonalWeight k := by
  unfold concreteL2R2DiagonalWeight
  exact add_nonneg (Nat.cast_nonneg k) zero_le_one

/-- The selected output coordinate is bounded above by the ambient output norm. -/
theorem concrete_l2_r2_dense_diagonal_domain_unit_probe_action_coord_le_norm
    (k : ℕ) :
    ‖concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDiagonalDomainUnitProbe k) k‖ ≤
      ‖concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDiagonalDomainUnitProbe k)‖ := by
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (concreteL2R2DenseDiagonalDomainLinearMap
      (concreteL2R2DenseDiagonalDomainUnitProbe k)) k

/-- The dense-domain diagonal action has norm at least the selected diagonal
weight on the coordinate-unit probe. -/
theorem concrete_l2_r2_dense_diagonal_domain_unit_probe_weight_le_action_norm
    (k : ℕ) :
    concreteL2R2DiagonalWeight k ≤
      ‖concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDiagonalDomainUnitProbe k)‖ := by
  have hcoord := concrete_l2_r2_dense_diagonal_domain_unit_probe_action_coord_self k
  have hnormCoord :
      ‖concreteL2R2DenseDiagonalDomainLinearMap
          (concreteL2R2DenseDiagonalDomainUnitProbe k) k‖ =
        concreteL2R2DiagonalWeight k := by
    rw [hcoord]
    exact norm_of_nonneg (concrete_l2_r2_diagonal_weight_nonneg k)
  calc
    concreteL2R2DiagonalWeight k =
        ‖concreteL2R2DenseDiagonalDomainLinearMap
          (concreteL2R2DenseDiagonalDomainUnitProbe k) k‖ := hnormCoord.symm
    _ ≤ ‖concreteL2R2DenseDiagonalDomainLinearMap
          (concreteL2R2DenseDiagonalDomainUnitProbe k)‖ :=
        concrete_l2_r2_dense_diagonal_domain_unit_probe_action_coord_le_norm k

/-- Unit-sphere unboundedness target for the R2 dense-domain diagonal operator. -/
def concreteL2R2DenseDomainOperatorUnboundednessQuantification : Prop :=
  ∀ B : ℝ, ∃ x : concreteL2R2DenseDiagonalDomainCarrier,
    ‖(x : ConcreteL2R1HilbertCarrier)‖ = 1 ∧
      B ≤ ‖concreteL2R2DenseDiagonalDomainLinearMap x‖

/-- The R2 dense-domain diagonal operator is unbounded on unit coordinate probes.

The proof chooses a coordinate `k` with `B < k`, uses the unit vector `e_k`, and
then reads the selected output coordinate `(k+1)e_k` as a lower bound for the
ambient output norm. -/
theorem concrete_l2_r2_dense_domain_operator_unboundedness_quantification :
    concreteL2R2DenseDomainOperatorUnboundednessQuantification := by
  intro B
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨concreteL2R2DenseDiagonalDomainUnitProbe k, ?_, ?_⟩
  · exact concrete_l2_r2_dense_diagonal_domain_unit_probe_norm_eq_one k
  · have hBweight : B ≤ concreteL2R2DiagonalWeight k := by
      unfold concreteL2R2DiagonalWeight
      exact le_trans (le_of_lt hk) (by nlinarith [Nat.cast_nonneg k])
    exact le_trans hBweight
      (concrete_l2_r2_dense_diagonal_domain_unit_probe_weight_le_action_norm k)

/-- Adapter predicate for the R2 dense-domain unboundedness layer. -/
def concreteL2R2DenseDiagonalDomainUnboundednessAdapter : Prop :=
  concreteL2R2DenseDomainOperatorUnboundednessQuantification ∧
  (∀ k : ℕ,
    ‖(concreteL2R2DenseDiagonalDomainUnitProbe k : ConcreteL2R1HilbertCarrier)‖ = 1) ∧
  (∀ k : ℕ,
    concreteL2R2DiagonalWeight k ≤
      ‖concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDiagonalDomainUnitProbe k)‖)

/-- Adapter theorem for R2 dense-domain unboundedness. -/
theorem concrete_l2_r2_dense_diagonal_domain_unboundedness_adapter_ready :
    concreteL2R2DenseDiagonalDomainUnboundednessAdapter := by
  exact ⟨
    concrete_l2_r2_dense_domain_operator_unboundedness_quantification,
    concrete_l2_r2_dense_diagonal_domain_unit_probe_norm_eq_one,
    concrete_l2_r2_dense_diagonal_domain_unit_probe_weight_le_action_norm⟩

/-- R2 dense-domain unboundedness surface.

This completes the dense-domain unbounded-Hamiltonian substrate: the operator is
a dense-domain Mathlib `LinearPMap`, has closed graph, and has unit probes whose
images exceed arbitrary real thresholds.  Self-adjointness and spectral/PVM
construction remain separate R3/R4 obligations. -/
structure ConcreteL2R2DenseDiagonalDomainUnboundednessSurface where
  linearPMapReady : concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady
  unboundednessReady : concreteL2R2DenseDomainOperatorUnboundednessQuantification
  unitProbeNormOne : ∀ k : ℕ,
    ‖(concreteL2R2DenseDiagonalDomainUnitProbe k : ConcreteL2R1HilbertCarrier)‖ = 1
  unitProbeWeightLeActionNorm : ∀ k : ℕ,
    concreteL2R2DiagonalWeight k ≤
      ‖concreteL2R2DenseDiagonalDomainLinearMap
        (concreteL2R2DenseDiagonalDomainUnitProbe k)‖
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2 dense-domain unboundedness surface. -/
def concreteL2R2DenseDiagonalDomainUnboundednessSurface :
    ConcreteL2R2DenseDiagonalDomainUnboundednessSurface :=
  { linearPMapReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_surface_ready
    unboundednessReady :=
      concrete_l2_r2_dense_domain_operator_unboundedness_quantification
    unitProbeNormOne := concrete_l2_r2_dense_diagonal_domain_unit_probe_norm_eq_one
    unitProbeWeightLeActionNorm :=
      concrete_l2_r2_dense_diagonal_domain_unit_probe_weight_le_action_norm
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the R2 dense-domain unboundedness surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainUnboundednessSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady ∧
  concreteL2R2DenseDiagonalDomainUnboundednessAdapter ∧
  concreteL2R2DenseDiagonalDomainUnboundednessSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DenseDiagonalDomainUnboundednessSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2DenseDiagonalDomainUnboundednessSurface.boundaryNotPVMConstruction ∧
  concreteL2R2DenseDiagonalDomainUnboundednessSurface.boundaryNotPositiveSpectralWeight

/-- The R2 dense-domain unboundedness surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_unboundedness_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainUnboundednessSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_unboundedness_adapter_ready,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker for the R2 dense-domain unboundedness surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainUnboundednessBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainUnboundednessSurfaceReady

/-- Boundary theorem for the R2 dense-domain unboundedness surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_unboundedness_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainUnboundednessBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_unboundedness_surface_ready

end

end MathlibAnalytic
end MGAP4D
