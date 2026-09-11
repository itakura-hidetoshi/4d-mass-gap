import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRationalSemigroup
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSMidpointNormInequality
import Mathlib.Tactic

/-!
# Symmetry and positivity of the factorial OS rational direct-limit semigroup

The same-root factorial midpoint identity is stronger than contractivity. At half time it gives the
standard OS factorization

`<T_h x, T_h y> = <x, T_(2h) y>`.

This file lifts that identity from finite-slot carrier vectors through separation, fixed-slot Hilbert
completion, the algebraic direct limit, and finally the completed direct limit. The factorization
immediately yields symmetry of every nonnegative-rational-time operator and positivity of its
quadratic form:

`<T_t x,y> = <x,T_t y>` and `<x,T_t x> = ||T_(t/2)x||^2 >= 0`.

No continuity in the time parameter is assumed or inferred. In particular this package does not
silently identify the rational semigroup with a real `C₀` semigroup.
-/

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

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

/-- Dense fixed-slot Hilbert states preserve the OS carrier inner product exactly. -/
@[simp]
theorem inner_hilbertState_hilbertState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F G : P.FixedSlotCarrier) :
    inner ℝ (P.hilbertState F) (P.hilbertState G) = inner ℝ F G := by
  change inner ℝ
      ((P.osClass F : Completion P.Separated))
      ((P.osClass G : Completion P.Separated)) = inner ℝ F G
  rw [Completion.inner_coe]
  change inner ℝ (SeparationQuotient.mk F) (SeparationQuotient.mk G) = inner ℝ F G
  exact SeparationQuotient.inner_mk_mk F G

/-- Exact carrier-level OS factorization in the common midpoint sector. -/
theorem fixedSlotCarrierTimeTranslate_inner_eq_common_midpoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F G : P.FixedSlotCarrier) :
    let K : PrimaryScalarFiniteNonnegativeSlotIndex :=
      ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
          P.slots t,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
          P.slots P.slots_nonneg t ht⟩
    let PK := P.fixedSlotDataOfIndex K
    let P2 := P.fixedSlotTimeTranslateData (t + t) (add_nonneg ht ht)
    let hleft : P.slots ⊆ PK.slots :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
        P.slots t
    let hfuture : P2.slots ⊆ PK.slots :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
        P.slots t
    inner ℝ
        (P.fixedSlotCarrierTimeTranslate t ht F)
        (P.fixedSlotCarrierTimeTranslate t ht G) =
      inner ℝ
        (P.fixedSlotCarrierInclusion PK hleft F)
        (P2.fixedSlotCarrierInclusion PK hfuture
          (P.fixedSlotCarrierTimeTranslate (t + t) (add_nonneg ht ht) G)) := by
  dsimp
  rw [(P.fixedSlotTimeTranslateData t ht).inner_eq_fixedSlotOSBilinForm]
  rw [(P.fixedSlotDataOfIndex
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
        P.slots t,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
        P.slots P.slots_nonneg t ht⟩).inner_eq_fixedSlotOSBilinForm]
  change
    L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t P.slots)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t F.observable)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t G.observable) =
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
            P.slots (t + t) G.observable))
  exact
    L.factorial_continuum_fixedSlotOSBilinForm_timeTranslate_eq_common_midpoint
      H N hN beta hbeta P.slots
      (fun q : P.slots => P.slots_nonneg q.1 q.2)
      t ht F.observable G.observable

/-- The exact midpoint factorization extends from dense carrier states to the fixed-slot Hilbert
completions. -/
theorem fixedSlotHilbertTimeTranslate_inner_eq_common_midpoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x y : P.Hilbert) :
    let K : PrimaryScalarFiniteNonnegativeSlotIndex :=
      ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
          P.slots t,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
          P.slots P.slots_nonneg t ht⟩
    let PK := P.fixedSlotDataOfIndex K
    let P2 := P.fixedSlotTimeTranslateData (t + t) (add_nonneg ht ht)
    let hleft : P.slots ⊆ PK.slots :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
        P.slots t
    let hfuture : P2.slots ⊆ PK.slots :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
        P.slots t
    inner ℝ
        (P.fixedSlotHilbertTimeTranslateCLM t ht x)
        (P.fixedSlotHilbertTimeTranslateCLM t ht y) =
      inner ℝ
        (P.fixedSlotHilbertInclusion PK hleft x)
        (P2.fixedSlotHilbertInclusion PK hfuture
          (P.fixedSlotHilbertTimeTranslateCLM (t + t) (add_nonneg ht ht) y)) := by
  dsimp
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((P.fixedSlotHilbertTimeTranslateCLM t ht).continuous.inner continuous_const)
        ((P.fixedSlotHilbertLinearIsometry
          (P.fixedSlotDataOfIndex
            ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                P.slots t,
              periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
                P.slots P.slots_nonneg t ht⟩)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
            P.slots t)).continuous.inner continuous_const)
  | ih x =>
      obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
      induction y using Completion.induction_on with
      | hp =>
          let K : PrimaryScalarFiniteNonnegativeSlotIndex :=
            ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                P.slots t,
              periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
                P.slots P.slots_nonneg t ht⟩
          let P2 := P.fixedSlotTimeTranslateData (t + t) (add_nonneg ht ht)
          let hfuture : P2.slots ⊆ (P.fixedSlotDataOfIndex K).slots :=
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
              P.slots t
          have hfutureContinuous : Continuous (fun y : P.Hilbert =>
              P2.fixedSlotHilbertLinearIsometry (P.fixedSlotDataOfIndex K) hfuture
                (P.fixedSlotHilbertTimeTranslateCLM
                  (t + t) (add_nonneg ht ht) y)) :=
            (P2.fixedSlotHilbertLinearIsometry
              (P.fixedSlotDataOfIndex K) hfuture).continuous.comp
              (P.fixedSlotHilbertTimeTranslateCLM
                (t + t) (add_nonneg ht ht)).continuous
          exact isClosed_eq
            (continuous_const.inner
              (P.fixedSlotHilbertTimeTranslateCLM t ht).continuous)
            (continuous_const.inner hfutureContinuous)
      | ih y =>
          obtain ⟨G, rfl⟩ := SeparationQuotient.surjective_mk y
          change
            inner ℝ
                (P.fixedSlotHilbertTimeTranslateCLM t ht (P.hilbertState F))
                (P.fixedSlotHilbertTimeTranslateCLM t ht (P.hilbertState G)) =
              inner ℝ
                (P.fixedSlotHilbertInclusion
                  (P.fixedSlotDataOfIndex
                    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                        P.slots t,
                      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
                        P.slots P.slots_nonneg t ht⟩)
                  (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
                    P.slots t)
                  (P.hilbertState F))
                ((P.fixedSlotTimeTranslateData (t + t) (add_nonneg ht ht)).fixedSlotHilbertInclusion
                  (P.fixedSlotDataOfIndex
                    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                        P.slots t,
                      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
                        P.slots P.slots_nonneg t ht⟩)
                  (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
                    P.slots t)
                  (P.fixedSlotHilbertTimeTranslateCLM
                    (t + t) (add_nonneg ht ht) (P.hilbertState G)))
          rw [P.fixedSlotHilbertTimeTranslateCLM_hilbertState]
          rw [P.fixedSlotHilbertTimeTranslateCLM_hilbertState]
          rw [P.fixedSlotHilbertInclusion_hilbertState]
          rw [P.fixedSlotHilbertTimeTranslateCLM_hilbertState]
          rw [(P.fixedSlotTimeTranslateData
            (t + t) (add_nonneg ht ht)).fixedSlotHilbertInclusion_hilbertState]
          rw [(P.fixedSlotTimeTranslateData t ht).inner_hilbertState_hilbertState]
          rw [(P.fixedSlotDataOfIndex
            ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
                P.slots t,
              periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_nonneg
                P.slots P.slots_nonneg t ht⟩).inner_hilbertState_hilbertState]
          exact P.fixedSlotCarrierTimeTranslate_inner_eq_common_midpoint t ht F G

/-- Algebraic direct-limit midpoint factorization. -/
theorem fixedSlotHilbertAlgebraicTimeTranslate_inner_factorization
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    inner ℝ
        (P.fixedSlotHilbertAlgebraicTimeTranslate t ht z)
        (P.fixedSlotHilbertAlgebraicTimeTranslate t ht w) =
      inner ℝ z
        (P.fixedSlotHilbertAlgebraicTimeTranslate (t + t) (add_nonneg ht ht) w) := by
  obtain ⟨J, x, y, hx, hy⟩ := P.fixedSlotHilbertAlgebraic_exists_common_representation z w
  rw [← hx, ← hy]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  let Jt : PrimaryScalarFiniteNonnegativeSlotIndex :=
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J
  let J2 : PrimaryScalarFiniteNonnegativeSlotIndex :=
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate (t + t) (add_nonneg ht ht) J
  let M : PrimaryScalarFiniteNonnegativeSlotIndex :=
    ⟨J.1 ∪ J2.1, by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact J.2 q hq
      · exact J2.2 q hq⟩
  have hJ : J ≤ M := Finset.subset_union_left
  have hJ2 : J2 ≤ M := Finset.subset_union_right
  have hfactor :=
    (P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslate_inner_eq_common_midpoint
      t ht x y
  change
    inner ℝ
        (P.fixedSlotHilbertAlgebraicLinearIsometry Jt
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x))
        (P.fixedSlotHilbertAlgebraicLinearIsometry Jt
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht y)) =
      inner ℝ
        (P.fixedSlotHilbertAlgebraicOf J x)
        (P.fixedSlotHilbertAlgebraicOf J2
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
            (t + t) (add_nonneg ht ht) y))
  rw [P.fixedSlotHilbertAlgebraicLinearIsometry_inner]
  rw [← P.fixedSlotHilbertAlgebraicOf_map J M hJ x]
  rw [← P.fixedSlotHilbertAlgebraicOf_map J2 M hJ2
    ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
      (t + t) (add_nonneg ht ht) y)]
  change
    inner ℝ
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht y) =
      inner ℝ
        (P.fixedSlotHilbertAlgebraicLinearIsometry M
          (P.fixedSlotIndexedHilbertMap J M hJ x))
        (P.fixedSlotHilbertAlgebraicLinearIsometry M
          (P.fixedSlotIndexedHilbertMap J2 M hJ2
            ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
              (t + t) (add_nonneg ht ht) y)))
  rw [P.fixedSlotHilbertAlgebraicLinearIsometry_inner]
  change
    inner ℝ
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht y) =
      inner ℝ
        (P.fixedSlotIndexedHilbertMap J M hJ x)
        (P.fixedSlotIndexedHilbertMap J2 M hJ2
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
            (t + t) (add_nonneg ht ht) y))
  simpa [M, J2, fixedSlotIndexedHilbertMap, fixedSlotIndexedHilbertLinearIsometry,
    fixedSlotHilbertInclusion] using hfactor

/-- Completed direct-limit midpoint factorization. -/
theorem fixedSlotHilbertDirectLimitTimeTranslate_inner_factorization
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x y : P.fixedSlotHilbertDirectLimitCompletion) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht y) =
      inner ℝ x
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (t + t) (add_nonneg ht ht) y) := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
  | ih z =>
      induction y using Completion.induction_on with
      | hp =>
          exact isClosed_eq
            (continuous_const.inner
              (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht).continuous)
            (continuous_const.inner
              (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
                (t + t) (add_nonneg ht ht)).continuous)
      | ih w =>
          rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
          rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
          rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
          rw [Completion.inner_coe]
          rw [Completion.inner_coe]
          exact P.fixedSlotHilbertAlgebraicTimeTranslate_inner_factorization t ht z w

/-- Every nonnegative rational direct-limit OS translation is symmetric. -/
theorem fixedSlotHilbertDirectLimitTimeTranslate_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x y : P.fixedSlotHilbertDirectLimitCompletion) :
    inner ℝ (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) y =
      inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht y) := by
  let h : ℚ := t / 2
  have hh : 0 ≤ h := div_nonneg ht (by norm_num)
  have hdouble : h + h = t := by
    dsimp [h]
    ring
  have hxy := P.fixedSlotHilbertDirectLimitTimeTranslate_inner_factorization h hh x y
  have hyx := P.fixedSlotHilbertDirectLimitTimeTranslate_inner_factorization h hh y x
  have hxy' :
      inner ℝ
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh y) =
        inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht y) := by
    simpa [hdouble] using hxy
  have hyx' :
      inner ℝ
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh y)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x) =
        inner ℝ y (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) := by
    simpa [hdouble] using hyx
  calc
    inner ℝ (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) y =
        inner ℝ y (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) := by
      rw [real_inner_comm]
    _ = inner ℝ
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh y)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x) := hyx'.symm
    _ = inner ℝ
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh y) := by
      rw [real_inner_comm]
    _ = inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht y) := hxy'

/-- The rational OS quadratic form is the squared norm at half time. -/
theorem fixedSlotHilbertDirectLimitTimeTranslate_inner_self_eq_half_norm_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) =
      ‖P.fixedSlotHilbertDirectLimitTimeTranslateCLM (t / 2)
        (div_nonneg ht (by norm_num)) x‖ ^ 2 := by
  let h : ℚ := t / 2
  have hh : 0 ≤ h := div_nonneg ht (by norm_num)
  have hdouble : h + h = t := by
    dsimp [h]
    ring
  have hfac := P.fixedSlotHilbertDirectLimitTimeTranslate_inner_factorization h hh x x
  have hfac' :
      inner ℝ
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x) =
        inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) := by
    simpa [hdouble] using hfac
  calc
    inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) =
        inner ℝ
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x) := hfac'.symm
    _ = ‖P.fixedSlotHilbertDirectLimitTimeTranslateCLM h hh x‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    _ = ‖P.fixedSlotHilbertDirectLimitTimeTranslateCLM (t / 2)
        (div_nonneg ht (by norm_num)) x‖ ^ 2 := rfl

/-- Every rational-time OS translation is positive semidefinite as a quadratic form. -/
theorem fixedSlotHilbertDirectLimitTimeTranslate_inner_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    0 ≤ inner ℝ x (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) := by
  rw [P.fixedSlotHilbertDirectLimitTimeTranslate_inner_self_eq_half_norm_sq t ht x]
  positivity

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
