import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSSeparatedTimeTranslate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSCarrierIsometry
import Mathlib.Tactic

/-!
# Factorial OS midpoint norm inequality

The exact common-sector midpoint identity already gives

`B_{J+t}(T_t F,T_t F) = B_K(iF,iT_{2t}F)`

with `K = J ∪ (J+2t)`.  This file combines that identity with the real
Cauchy--Schwarz inequality in the existing seminormed inner-product carrier and
with the exact isometry of fixed-slot inclusions.  The result is the standard OS
midpoint estimate

`‖T_t F‖² ≤ ‖F‖ * ‖T_{2t} F‖`.

This is only the one-step midpoint inequality.  No iteration, contraction,
bounded operator, Hilbert-completion extension, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The factorial same-root OS midpoint identity implies the standard log-convex one-step norm
estimate for fixed-slot carrier translation. -/
theorem fixedSlotCarrierTimeTranslate_norm_sq_le_mul_norm_double
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ^ 2 ≤
      ‖F‖ *
        ‖P.fixedSlotCarrierTimeTranslate (t + t) (add_nonneg ht ht) F‖ := by
  let K : PrimaryScalarFiniteNonnegativeSlotIndex :=
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
        P.slots t,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
        P.slots P.slots_nonneg t ht⟩
  let PK := P.fixedSlotDataOfIndex K
  let P2 := P.fixedSlotTimeTranslateData (t + t) (add_nonneg ht ht)
  have hleft : P.slots ⊆ PK.slots := by
    change P.slots ⊆
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
        P.slots t
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
        P.slots t
  have hfuture : P2.slots ⊆ PK.slots := by
    change
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          (t + t) P.slots ⊆
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
          P.slots t
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
        P.slots t
  let X : PK.FixedSlotCarrier := P.fixedSlotCarrierInclusion PK hleft F
  let T2F : P2.FixedSlotCarrier :=
    P.fixedSlotCarrierTimeTranslate (t + t) (add_nonneg ht ht) F
  let Y : PK.FixedSlotCarrier := P2.fixedSlotCarrierInclusion PK hfuture T2F
  have hmid :
      ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ^ 2 = inner ℝ X Y := by
    calc
      ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ^ 2 =
          inner ℝ
            (P.fixedSlotCarrierTimeTranslate t ht F)
            (P.fixedSlotCarrierTimeTranslate t ht F) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = L.fixedSlotOSBilinForm H N hN beta hbeta
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
              t P.slots)
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
              P.slots t F.observable)
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
              P.slots t F.observable) := by
        exact (P.fixedSlotTimeTranslateData t ht).inner_eq_fixedSlotOSBilinForm _ _
      _ = L.fixedSlotOSBilinForm H N hN beta hbeta
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
              P.slots t)
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
              P.slots
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                P.slots t)
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
                P.slots t)
              F.observable)
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
                (t + t) P.slots)
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                P.slots t)
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
                P.slots t)
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
                P.slots (t + t) F.observable)) := by
        exact
          L.factorial_continuum_fixedSlotOSBilinForm_timeTranslate_eq_common_midpoint
            H N hN beta hbeta P.slots
            (fun q : P.slots => P.slots_nonneg q.1 q.2)
            t ht F.observable F.observable
      _ = inner ℝ X Y := by
        have hinner := PK.inner_eq_fixedSlotOSBilinForm X Y
        change
          inner ℝ X Y =
            L.fixedSlotOSBilinForm H N hN beta hbeta
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                P.slots t)
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
                P.slots
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                  P.slots t)
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
                  P.slots t)
                F.observable)
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
                  (t + t) P.slots)
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                  P.slots t)
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
                  P.slots t)
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
                  P.slots (t + t) F.observable)) at hinner
        exact hinner.symm
  calc
    ‖P.fixedSlotCarrierTimeTranslate t ht F‖ ^ 2 = inner ℝ X Y := hmid
    _ ≤ |inner ℝ X Y| := le_abs_self _
    _ ≤ ‖X‖ * ‖Y‖ := abs_real_inner_le_norm X Y
    _ = ‖F‖ * ‖P.fixedSlotCarrierTimeTranslate (t + t) (add_nonneg ht ht) F‖ := by
      rw [P.fixedSlotCarrierInclusion_norm PK hleft F]
      change ‖F‖ * ‖P2.fixedSlotCarrierInclusion PK hfuture T2F‖ = _
      rw [P2.fixedSlotCarrierInclusion_norm PK hfuture T2F]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
