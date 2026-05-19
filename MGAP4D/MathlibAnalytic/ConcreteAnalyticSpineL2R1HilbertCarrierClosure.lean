import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibCoordinateTransport

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- R1 canonical completed real `ℓ²` carrier, using Mathlib's completed
`lp`/`l2Space` infrastructure rather than a hand-rolled completion. -/
abbrev ConcreteL2R1HilbertCarrier : Type :=
  lp (fun _ : ℕ => ℝ) 2

/-- The zero vector in the R1 Mathlib completed carrier. -/
def concreteL2R1HilbertZero : ConcreteL2R1HilbertCarrier :=
  0

/-- R1 inherits its normed additive group structure from Mathlib. -/
theorem concrete_l2_r1_hilbert_has_normed_add_comm_group :
    Nonempty (NormedAddCommGroup ConcreteL2R1HilbertCarrier) := by
  exact ⟨inferInstance⟩

/-- R1 inherits its real inner-product space structure from Mathlib. -/
theorem concrete_l2_r1_hilbert_has_inner_product_space :
    Nonempty (InnerProductSpace ℝ ConcreteL2R1HilbertCarrier) := by
  exact ⟨inferInstance⟩

/-- R1 inherits completeness from Mathlib. -/
theorem concrete_l2_r1_hilbert_has_complete_space :
    Nonempty (CompleteSpace ConcreteL2R1HilbertCarrier) := by
  exact ⟨inferInstance⟩

/-- Mathlib coordinate units are norm-one vectors in the R1 carrier. -/
theorem concrete_l2_r1_hilbert_unit_norm_one (k : ℕ) :
    ‖(concreteL2MathlibUnit k : ConcreteL2R1HilbertCarrier)‖ = 1 := by
  exact concrete_l2_mathlib_unit_norm_eq_one k

/-- R1 has an explicit norm-one witness. -/
theorem concrete_l2_r1_hilbert_has_norm_one_witness :
    ∃ u : ConcreteL2R1HilbertCarrier, ‖u‖ = 1 := by
  exact ⟨concreteL2MathlibUnit 0, concrete_l2_r1_hilbert_unit_norm_one 0⟩

/-- R1 closure surface: completed real `ℓ²` carrier plus coordinate transport
from the finite-support computation lane.  Operator and spectral obligations are
kept outside this R1 unit. -/
structure ConcreteL2R1HilbertCarrierClosureSurface where
  carrier : Type
  carrierIsMathlibCompletedL2 : carrier = ConcreteL2R1HilbertCarrier
  zero : carrier
  hasNormedAddCommGroup : Nonempty (NormedAddCommGroup carrier)
  hasInnerProductSpace : Nonempty (InnerProductSpace ℝ carrier)
  hasCompleteSpace : Nonempty (CompleteSpace carrier)
  hasNormOneWitness : ∃ u : ConcreteL2R1HilbertCarrier, ‖u‖ = 1
  coordinateTransportReady : concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady
  boundaryNotR2Operator : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralLayer : Prop

/-- Concrete R1 Hilbert-carrier closure surface. -/
def concreteL2R1HilbertCarrierClosureSurface :
    ConcreteL2R1HilbertCarrierClosureSurface :=
  { carrier := ConcreteL2R1HilbertCarrier
    carrierIsMathlibCompletedL2 := rfl
    zero := concreteL2R1HilbertZero
    hasNormedAddCommGroup := concrete_l2_r1_hilbert_has_normed_add_comm_group
    hasInnerProductSpace := concrete_l2_r1_hilbert_has_inner_product_space
    hasCompleteSpace := concrete_l2_r1_hilbert_has_complete_space
    hasNormOneWitness := concrete_l2_r1_hilbert_has_norm_one_witness
    coordinateTransportReady :=
      concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready
    boundaryNotR2Operator := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralLayer := True }

/-- R1 readiness predicate. -/
def concreteAnalyticSpineL2R1HilbertCarrierClosureSurfaceReady : Prop :=
  Nonempty (NormedAddCommGroup ConcreteL2R1HilbertCarrier) ∧
  Nonempty (InnerProductSpace ℝ ConcreteL2R1HilbertCarrier) ∧
  Nonempty (CompleteSpace ConcreteL2R1HilbertCarrier) ∧
  (∃ u : ConcreteL2R1HilbertCarrier, ‖u‖ = 1) ∧
  concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady ∧
  concreteL2R1HilbertCarrierClosureSurface.boundaryNotR2Operator ∧
  concreteL2R1HilbertCarrierClosureSurface.boundaryNotSelfAdjointness ∧
  concreteL2R1HilbertCarrierClosureSurface.boundaryNotSpectralLayer

/-- R1 closure theorem. -/
theorem concrete_analytic_spine_l2_r1_hilbert_carrier_closure_surface_ready :
    concreteAnalyticSpineL2R1HilbertCarrierClosureSurfaceReady := by
  unfold concreteAnalyticSpineL2R1HilbertCarrierClosureSurfaceReady
  exact And.intro concrete_l2_r1_hilbert_has_normed_add_comm_group <|
    And.intro concrete_l2_r1_hilbert_has_inner_product_space <|
      And.intro concrete_l2_r1_hilbert_has_complete_space <|
        And.intro concrete_l2_r1_hilbert_has_norm_one_witness <|
          And.intro
            concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R1 completed Hilbert-carrier closure. -/
def concreteAnalyticSpineL2R1HilbertCarrierClosureHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R1HilbertCarrierClosureSurfaceReady

/-- Boundary theorem for the R1 completed Hilbert-carrier closure. -/
theorem concrete_analytic_spine_l2_r1_hilbert_carrier_closure_hard_residual_boundary_held :
    concreteAnalyticSpineL2R1HilbertCarrierClosureHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r1_hilbert_carrier_closure_surface_ready

end

end MathlibAnalytic
end MGAP4D
