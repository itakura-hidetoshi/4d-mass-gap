import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSCommonSectorMidpoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSCarrierIsometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSHilbertIndexedSystem
import Mathlib.Tactic

/-!
# Factorial OS time translation preserves fixed-slot null vectors

The preceding common-sector midpoint identity rewrites the translated OS quadratic form on `J+t`
as a mixed OS form in the single finite sector

`K = J ∪ (J+2t)`.

If the original vector is OS-null on `J`, its canonical inclusion into `K` is still null because
fixed-slot inclusion is already a linear isometry.  Mathlib's seminormed-inner-product theorem
`inner_eq_zero_of_left` then kills the mixed common-sector inner product against the arbitrary
`J+2t` factor.  Hence the time-translated observable is null on `J+t`.

This is the first null-space statement on the same primary-scalar Wilson/Prokhorov root.  No
separation-quotient lift, contraction estimate, semigroup, Hamiltonian, spectral statement, or
mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The midpoint common sector remains nonnegative when the original slots and the shift are
nonnegative. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
    (J : Finset ℚ)
    (hJ : ∀ q ∈ J, (0 : ℚ) ≤ q)
    (t : ℚ) (ht : 0 ≤ t) :
    ∀ q ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t,
      (0 : ℚ) ≤ q := by
  intro q hq
  change q ∈
    J ∪
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
        (t + t) J at hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hJ q hq
  · exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_nonneg
        (t + t) (add_nonneg ht ht) J hJ q hq

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Canonical fixed-slot OS datum obtained by translating every slot of `P` by a nonnegative
rational time `t`.  The global analytic data are inherited unchanged from `P`. -/
def fixedSlotTimeTranslateData
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L :=
  P.fixedSlotDataOfIndex
    (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht P.fixedSlotIndex)

@[simp]
theorem fixedSlotTimeTranslateData_slots
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    (P.fixedSlotTimeTranslateData t ht).slots =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
        t P.slots :=
  rfl

/-- Linear transport of wrapped fixed-slot OS carriers along rational-time translation.  No norm
bound is claimed here. -/
noncomputable def fixedSlotCarrierTimeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.FixedSlotCarrier →ₗ[ℝ] (P.fixedSlotTimeTranslateData t ht).FixedSlotCarrier where
  toFun F :=
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
      P.slots t F.observable⟩
  map_add' F G := by
    apply FixedSlotCarrier.observable_injective (P.fixedSlotTimeTranslateData t ht)
    change
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t (F.observable + G.observable) =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            P.slots t F.observable +
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            P.slots t G.observable
    exact map_add _ _ _
  map_smul' r F := by
    apply FixedSlotCarrier.observable_injective (P.fixedSlotTimeTranslateData t ht)
    change
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t (r • F.observable) =
        r • periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t F.observable
    exact map_smul _ _ _

@[simp]
theorem fixedSlotCarrierTimeTranslate_observable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    (P.fixedSlotCarrierTimeTranslate t ht F).observable =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
        P.slots t F.observable :=
  rfl

/-- On canonical factorial spacing, nonnegative rational time translation sends every fixed-slot OS
null vector to a null vector in the translated slot sector. -/
theorem fixedSlotCarrierTimeTranslate_mem_nullSubmodule
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier)
    (hF : F ∈ P.nullSubmodule) :
    P.fixedSlotCarrierTimeTranslate t ht F ∈
      (P.fixedSlotTimeTranslateData t ht).nullSubmodule := by
  let K : PrimaryScalarFiniteNonnegativeSlotIndex :=
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
        P.slots t,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
        P.slots P.slots_nonneg t ht⟩
  let PK := P.fixedSlotDataOfIndex K
  have hleft : P.slots ⊆ PK.slots := by
    change P.slots ⊆
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
        P.slots t
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
        P.slots t
  have hfuture :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          (t + t) P.slots ⊆ PK.slots := by
    change
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          (t + t) P.slots ⊆
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
          P.slots t
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
        P.slots t
  let X : PK.FixedSlotCarrier := P.fixedSlotCarrierInclusion PK hleft F
  let Y : PK.FixedSlotCarrier :=
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          (t + t) P.slots)
        PK.slots hfuture
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots (t + t) F.observable)⟩
  have hXnull : X ∈ PK.nullSubmodule := by
    dsimp [X]
    exact (P.mem_nullSubmodule_fixedSlotCarrierInclusion_iff PK hleft F).2 hF
  have hXnorm : ‖X‖ = 0 :=
    (PK.mem_nullSubmodule X).1 hXnull
  have hXY : inner ℝ X Y = 0 :=
    inner_eq_zero_of_left Y hXnorm
  apply
    ((P.fixedSlotTimeTranslateData t ht).mem_nullSubmodule_iff_osQuadratic_eq_zero
      (P.fixedSlotCarrierTimeTranslate t ht F)).2
  change
    L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          t P.slots)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t F.observable)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t F.observable) = 0
  calc
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
    _ = 0 := hXY

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
