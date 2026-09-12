import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSMidpointNormInequality
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# Uniform fixed-slot OS norm bound from the observable sup norm

For every fixed nonnegative slot sector, the OS seminorm is bounded by the ambient supremum norm of
the bounded-continuous observable.  Indeed, the OS quadratic form is the expectation of

`(Theta F) * F`,

and probability integration, reflection pullback, and finite-slot pullback are all norm
nonincreasing at the bounded-continuous-function level.  Hence

`‖F‖_OS ≤ ‖F.observable‖_∞`.

Combining this generic estimate with the already-canonical fixed-slot time-translation pullback
gives the shift-independent bound

`‖T_t F‖_OS ≤ ‖F.observable‖_∞`

for every nonnegative rational shift on the factorial root.  This is the uniform far-time bound
needed to turn the midpoint inequality into contraction in the next layer.

No contraction, iteration, Hilbert-completion extension, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {latticeSpacing : ℕ → ℝ}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta latticeSpacing}

/-- The OS seminorm squared of a fixed-slot carrier is bounded by the square of the ambient
bounded-continuous observable norm. -/
theorem fixedSlotCarrier_norm_sq_le_observable_norm_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) :
    ‖F‖ ^ 2 ≤ ‖F.observable‖ ^ 2 := by
  let f : BoundedContinuousFunction (ℚ → ℝ) ℝ :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
      P.slots F.observable
  let rf : BoundedContinuousFunction (ℚ → ℝ) ℝ :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback f
  let h : BoundedContinuousFunction (ℚ → ℝ) ℝ := rf * f
  have hf : ‖f‖ ≤ ‖F.observable‖ := by
    dsimp [f, periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable]
    exact BoundedContinuousFunction.norm_compContinuous_le _ _
  have hrf : ‖rf‖ ≤ ‖f‖ := by
    dsimp [rf, periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback]
    exact BoundedContinuousFunction.norm_compContinuous_le _ _
  have hint :
      ‖∫ x, h x ∂(L.continuumMeasure : Measure (ℚ → ℝ))‖ ≤ ‖h‖ :=
    h.norm_integral_le_norm (L.continuumMeasure : Measure (ℚ → ℝ))
  calc
    ‖F‖ ^ 2 = inner ℝ F F := (real_inner_self_eq_norm_sq F).symm
    _ = ∫ x, h x ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
      rw [P.inner_eq_fixedSlotOSBilinForm]
      rw [L.fixedSlotOSBilinForm_apply]
      rfl
    _ ≤ |∫ x, h x ∂(L.continuumMeasure : Measure (ℚ → ℝ))| := le_abs_self _
    _ = ‖∫ x, h x ∂(L.continuumMeasure : Measure (ℚ → ℝ))‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖h‖ := hint
    _ ≤ ‖rf‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ ‖f‖ * ‖f‖ :=
      mul_le_mul_of_nonneg_right hrf (norm_nonneg f)
    _ ≤ ‖F.observable‖ * ‖F.observable‖ := by
      exact mul_self_le_mul_self (norm_nonneg f) hf
    _ = ‖F.observable‖ ^ 2 := by ring

/-- The OS seminorm itself is bounded by the ambient supremum norm of the wrapped observable. -/
theorem fixedSlotCarrier_norm_le_observable_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) :
    ‖F‖ ≤ ‖F.observable‖ := by
  exact le_of_sq_le_sq (P.fixedSlotCarrier_norm_sq_le_observable_norm_sq F) (norm_nonneg _)

variable {Lfac :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- On the canonical factorial root, every nonnegative rational translate has OS seminorm bounded
by the same original observable sup norm, independently of the shift. -/
theorem fixedSlotCarrierTimeTranslate_norm_le_observable_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing Lfac)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ≤ ‖F.observable‖ := by
  calc
    ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ≤
        ‖(P.fixedSlotCarrierTimeTranslate t ht F).observable‖ :=
      (P.fixedSlotTimeTranslateData t ht).fixedSlotCarrier_norm_le_observable_norm _
    _ =
        ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t F.observable‖ := rfl
    _ ≤ ‖F.observable‖ := by
      dsimp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate]
      exact BoundedContinuousFunction.norm_compContinuous_le _ _

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
