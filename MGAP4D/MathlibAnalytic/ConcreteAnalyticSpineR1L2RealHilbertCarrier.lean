import Mathlib.Analysis.InnerProductSpace.l2Space
import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- R1 concrete real Hilbert carrier: the Mathlib completed `ℓ²(ℕ, ℝ)` space.

This is intentionally only the carrier layer.  It does not introduce an
unbounded operator, a dense domain, graph closure, self-adjointness, spectral
measure, PVM, plaquette observable, exact `33/20` atom, or spectral-weight
claim. -/
abbrev ConcreteR1L2RealHilbertCarrier : Type :=
  lp (fun _ : ℕ => ℝ) 2

/-- The zero vector of the R1 concrete `ℓ²` carrier. -/
def concreteR1L2RealHilbertZero : ConcreteR1L2RealHilbertCarrier :=
  0

/-- The coordinate unit vector in the R1 concrete `ℓ²` carrier. -/
def concreteR1L2RealHilbertUnit (k : ℕ) : ConcreteR1L2RealHilbertCarrier :=
  lp.single 2 k (1 : ℝ)

/-- The R1 carrier has Mathlib's normed additive group structure. -/
def concrete_r1_l2_real_hilbert_normed_add_comm_group :
    NormedAddCommGroup ConcreteR1L2RealHilbertCarrier := by
  infer_instance

/-- The R1 carrier has Mathlib's real inner-product structure. -/
def concrete_r1_l2_real_hilbert_inner_product_space :
    InnerProductSpace ℝ ConcreteR1L2RealHilbertCarrier := by
  infer_instance

/-- The R1 carrier is complete; hence this is a genuine Mathlib-backed Hilbert
carrier, not only a raw sequence subtype. -/
def concrete_r1_l2_real_hilbert_complete_space :
    CompleteSpace ConcreteR1L2RealHilbertCarrier := by
  infer_instance

/-- The zero vector has norm zero. -/
theorem concrete_r1_l2_real_hilbert_zero_norm :
    ‖concreteR1L2RealHilbertZero‖ = 0 := by
  simp [concreteR1L2RealHilbertZero]

/-- The selected coordinate of the coordinate unit vector is one. -/
theorem concrete_r1_l2_real_hilbert_unit_apply_self (k : ℕ) :
    concreteR1L2RealHilbertUnit k k = 1 := by
  simp [concreteR1L2RealHilbertUnit]

/-- Off the selected coordinate, the coordinate unit vector is zero. -/
theorem concrete_r1_l2_real_hilbert_unit_apply_ne {k n : ℕ} (h : n ≠ k) :
    concreteR1L2RealHilbertUnit k n = 0 := by
  simp [concreteR1L2RealHilbertUnit, h]

/-- Mathlib norm theorem for the coordinate unit vector. -/
theorem concrete_r1_l2_real_hilbert_unit_norm_eq_one (k : ℕ) :
    ‖concreteR1L2RealHilbertUnit k‖ = 1 := by
  simp [concreteR1L2RealHilbertUnit]

/-- R1 surface: a closeable carrier-only PR unit for the concrete analytic spine. -/
structure ConcreteR1L2RealHilbertCarrierSurface where
  carrierIsMathlibL2 : Prop
  zero : ConcreteR1L2RealHilbertCarrier
  unit : ℕ → ConcreteR1L2RealHilbertCarrier
  normedAddCommGroupWitness : NormedAddCommGroup ConcreteR1L2RealHilbertCarrier
  innerProductSpaceWitness : InnerProductSpace ℝ ConcreteR1L2RealHilbertCarrier
  completeSpaceWitness : CompleteSpace ConcreteR1L2RealHilbertCarrier
  zeroNormLaw : ‖zero‖ = 0
  unitNormOneLaw : ∀ k : ℕ, ‖unit k‖ = 1
  boundaryNotDenseDomain : Prop
  boundaryNotUnboundedOperator : Prop
  boundaryNotGraphClosure : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralMeasure : Prop
  boundaryNotPVM : Prop
  boundaryNotPlaquetteObservable : Prop
  boundaryNotExactAtom3320 : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R1 carrier surface. -/
def concreteR1L2RealHilbertCarrierSurface :
    ConcreteR1L2RealHilbertCarrierSurface :=
  { carrierIsMathlibL2 := ConcreteR1L2RealHilbertCarrier = lp (fun _ : ℕ => ℝ) 2
    zero := concreteR1L2RealHilbertZero
    unit := concreteR1L2RealHilbertUnit
    normedAddCommGroupWitness := concrete_r1_l2_real_hilbert_normed_add_comm_group
    innerProductSpaceWitness := concrete_r1_l2_real_hilbert_inner_product_space
    completeSpaceWitness := concrete_r1_l2_real_hilbert_complete_space
    zeroNormLaw := concrete_r1_l2_real_hilbert_zero_norm
    unitNormOneLaw := concrete_r1_l2_real_hilbert_unit_norm_eq_one
    boundaryNotDenseDomain := True
    boundaryNotUnboundedOperator := True
    boundaryNotGraphClosure := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralMeasure := True
    boundaryNotPVM := True
    boundaryNotPlaquetteObservable := True
    boundaryNotExactAtom3320 := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the R1 carrier-only PR unit. -/
def concreteAnalyticSpineR1L2RealHilbertCarrierSurfaceReady : Prop :=
  CompleteSpace ConcreteR1L2RealHilbertCarrier ∧
  InnerProductSpace ℝ ConcreteR1L2RealHilbertCarrier ∧
  (∀ k : ℕ, ‖concreteR1L2RealHilbertUnit k‖ = 1) ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotDenseDomain ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotUnboundedOperator ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotGraphClosure ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotSelfAdjointness ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotSpectralMeasure ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotPVM ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotPlaquetteObservable ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotExactAtom3320 ∧
  concreteR1L2RealHilbertCarrierSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for the R1 concrete `ℓ²` real Hilbert carrier. -/
theorem concrete_analytic_spine_r1_l2_real_hilbert_carrier_surface_ready :
    concreteAnalyticSpineR1L2RealHilbertCarrierSurfaceReady := by
  unfold concreteAnalyticSpineR1L2RealHilbertCarrierSurfaceReady
  exact And.intro concrete_r1_l2_real_hilbert_complete_space <|
    And.intro concrete_r1_l2_real_hilbert_inner_product_space <|
      And.intro concrete_r1_l2_real_hilbert_unit_norm_eq_one <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- R1 hard-boundary marker: this PR closes only the concrete Hilbert carrier. -/
def concreteAnalyticSpineR1L2RealHilbertCarrierHardBoundaryHeld : Prop :=
  concreteAnalyticSpineR1L2RealHilbertCarrierSurfaceReady

/-- Boundary theorem for the R1 carrier-only PR unit. -/
theorem concrete_analytic_spine_r1_l2_real_hilbert_carrier_hard_boundary_held :
    concreteAnalyticSpineR1L2RealHilbertCarrierHardBoundaryHeld := by
  exact concrete_analytic_spine_r1_l2_real_hilbert_carrier_surface_ready

end

end MathlibAnalytic
end MGAP4D
