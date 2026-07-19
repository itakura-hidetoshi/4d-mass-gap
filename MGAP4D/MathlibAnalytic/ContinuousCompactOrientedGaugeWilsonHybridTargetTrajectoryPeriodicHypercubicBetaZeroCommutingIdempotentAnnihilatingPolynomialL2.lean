import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCommutingFluctuationProjectionFamilyL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The operator falling factorial

`T (T - I) ... (T - n I)`

written as an ordered composition of continuous linear endomorphisms.  The order
is immaterial for these scalar translates of one operator, but the recursive
form is convenient for induction in a noncommutative endomorphism algebra. -/
noncomputable def continuousLinearMapFallingFactorialL2
    (T : V →L[ℝ] V) : ℕ → V →L[ℝ] V
  | 0 => T
  | n + 1 =>
      (T - (((n + 1 : ℕ) : ℝ) • ContinuousLinearMap.id ℝ V)).comp
        (continuousLinearMapFallingFactorialL2 T n)

@[simp]
theorem continuousLinearMapFallingFactorialL2_zero
    (T : V →L[ℝ] V) :
    continuousLinearMapFallingFactorialL2 T 0 = T := by
  rfl

@[simp]
theorem continuousLinearMapFallingFactorialL2_succ_apply
    (T : V →L[ℝ] V)
    (n : ℕ)
    (f : V) :
    continuousLinearMapFallingFactorialL2 T (n + 1) f =
      T (continuousLinearMapFallingFactorialL2 T n f) -
        (((n + 1 : ℕ) : ℝ) • continuousLinearMapFallingFactorialL2 T n f) := by
  rfl

/-- Every falling-factorial polynomial in `T` commutes pointwise with an
endomorphism commuting with `T`. -/
theorem continuousLinearMapFallingFactorialL2_commute_apply
    (T Q : V →L[ℝ] V)
    (hComm : ∀ f : V, Q (T f) = T (Q f))
    (n : ℕ)
    (f : V) :
    Q (continuousLinearMapFallingFactorialL2 T n f) =
      continuousLinearMapFallingFactorialL2 T n (Q f) := by
  induction n with
  | zero =>
      exact hComm f
  | succ n ih =>
      rw [continuousLinearMapFallingFactorialL2_succ_apply,
        continuousLinearMapFallingFactorialL2_succ_apply,
        map_sub, map_smul, hComm, ih]

/-- On the kernel of a commuting idempotent summand `Q`, adding `Q` does not
change any falling-factorial operator polynomial. -/
theorem continuousLinearMapFallingFactorialL2_add_eq_of_left_eq_zero
    (T Q : V →L[ℝ] V)
    (hComm : ∀ f : V, Q (T f) = T (Q f))
    (n : ℕ)
    (f : V)
    (hQf : Q f = 0) :
    continuousLinearMapFallingFactorialL2 (Q + T) n f =
      continuousLinearMapFallingFactorialL2 T n f := by
  induction n with
  | zero =>
      change Q f + T f = T f
      rw [hQf, zero_add]
  | succ n ih =>
      rw [continuousLinearMapFallingFactorialL2_succ_apply,
        continuousLinearMapFallingFactorialL2_succ_apply, ih]
      have hQfalling :
          Q (continuousLinearMapFallingFactorialL2 T n f) = 0 := by
        calc
          Q (continuousLinearMapFallingFactorialL2 T n f) =
              continuousLinearMapFallingFactorialL2 T n (Q f) :=
            continuousLinearMapFallingFactorialL2_commute_apply
              T Q hComm n f
          _ = 0 := by rw [hQf]; exact map_zero _
      change
        Q (continuousLinearMapFallingFactorialL2 T n f) +
              T (continuousLinearMapFallingFactorialL2 T n f) -
            (((n + 1 : ℕ) : ℝ) •
              continuousLinearMapFallingFactorialL2 T n f) =
          T (continuousLinearMapFallingFactorialL2 T n f) -
            (((n + 1 : ℕ) : ℝ) •
              continuousLinearMapFallingFactorialL2 T n f)
      rw [hQfalling, zero_add]

/-- On the fixed space of a commuting idempotent summand `Q`, the next
falling-factorial polynomial of `Q + T` is the previous polynomial of `T`
followed by the remaining shifted factor `T + I`. -/
theorem continuousLinearMapFallingFactorialL2_add_succ_eq_shift_of_left_eq_self
    (T Q : V →L[ℝ] V)
    (hComm : ∀ f : V, Q (T f) = T (Q f))
    (n : ℕ)
    (f : V)
    (hQf : Q f = f) :
    continuousLinearMapFallingFactorialL2 (Q + T) (n + 1) f =
      (T + ContinuousLinearMap.id ℝ V)
        (continuousLinearMapFallingFactorialL2 T n f) := by
  induction n with
  | zero =>
      rw [continuousLinearMapFallingFactorialL2_succ_apply]
      simp only [continuousLinearMapFallingFactorialL2_zero]
      have hAddApply (g : V) : (Q + T) g = Q g + T g := by
        rfl
      have hShiftApply (g : V) :
          (T + ContinuousLinearMap.id ℝ V) g = T g + g := by
        rfl
      rw [hAddApply ((Q + T) f), hAddApply f, hShiftApply (T f)]
      simp only [map_add, hQf, hComm, one_smul]
      module
  | succ n ih =>
      rw [continuousLinearMapFallingFactorialL2_succ_apply, ih,
        continuousLinearMapFallingFactorialL2_succ_apply]
      have hQfalling :
          Q (continuousLinearMapFallingFactorialL2 T n f) =
            continuousLinearMapFallingFactorialL2 T n f := by
        calc
          Q (continuousLinearMapFallingFactorialL2 T n f) =
              continuousLinearMapFallingFactorialL2 T n (Q f) :=
            continuousLinearMapFallingFactorialL2_commute_apply
              T Q hComm n f
          _ = continuousLinearMapFallingFactorialL2 T n f := by rw [hQf]
      have hQshift :
          Q ((T + ContinuousLinearMap.id ℝ V)
              (continuousLinearMapFallingFactorialL2 T n f)) =
            (T + ContinuousLinearMap.id ℝ V)
              (continuousLinearMapFallingFactorialL2 T n f) := by
        change
          Q (T (continuousLinearMapFallingFactorialL2 T n f) +
              continuousLinearMapFallingFactorialL2 T n f) =
            T (continuousLinearMapFallingFactorialL2 T n f) +
              continuousLinearMapFallingFactorialL2 T n f
        rw [map_add, hComm, hQfalling]
      calc
        Q ((T + ContinuousLinearMap.id ℝ V)
              (continuousLinearMapFallingFactorialL2 T n f)) +
              T ((T + ContinuousLinearMap.id ℝ V)
                (continuousLinearMapFallingFactorialL2 T n f)) -
            (((n + 2 : ℕ) : ℝ) •
              (T + ContinuousLinearMap.id ℝ V)
                (continuousLinearMapFallingFactorialL2 T n f)) =
          T ((T + ContinuousLinearMap.id ℝ V)
                (continuousLinearMapFallingFactorialL2 T n f)) -
            (((n + 1 : ℕ) : ℝ) •
              (T + ContinuousLinearMap.id ℝ V)
                (continuousLinearMapFallingFactorialL2 T n f)) := by
            rw [hQshift]
            module
        _ = (T + ContinuousLinearMap.id ℝ V)
              (T (continuousLinearMapFallingFactorialL2 T n f) -
                (((n + 1 : ℕ) : ℝ) •
                  continuousLinearMapFallingFactorialL2 T n f)) := by
            change
              T (T (continuousLinearMapFallingFactorialL2 T n f) +
                    continuousLinearMapFallingFactorialL2 T n f) -
                  (((n + 1 : ℕ) : ℝ) •
                    (T (continuousLinearMapFallingFactorialL2 T n f) +
                      continuousLinearMapFallingFactorialL2 T n f)) =
                T (T (continuousLinearMapFallingFactorialL2 T n f) -
                    (((n + 1 : ℕ) : ℝ) •
                      continuousLinearMapFallingFactorialL2 T n f)) +
                  (T (continuousLinearMapFallingFactorialL2 T n f) -
                    (((n + 1 : ℕ) : ℝ) •
                      continuousLinearMapFallingFactorialL2 T n f))
            rw [map_add, map_sub, map_smul]
            module

/-- Adjoining one commuting idempotent to a sum whose degree-`n+1` falling
factorial vanishes makes the degree-`n+2` falling factorial vanish. -/
theorem continuousLinearMapFallingFactorialL2_add_idempotent_succ_eq_zero
    (T Q : V →L[ℝ] V)
    (hComm : ∀ f : V, Q (T f) = T (Q f))
    (hIdempotent : ∀ f : V, Q (Q f) = Q f)
    (n : ℕ)
    (hAnnihilates : continuousLinearMapFallingFactorialL2 T n = 0) :
    continuousLinearMapFallingFactorialL2 (Q + T) (n + 1) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  let kernelPart : V := f - Q f
  let fixedPart : V := Q f
  have hDecompose : kernelPart + fixedPart = f := by
    dsimp [kernelPart, fixedPart]
    abel
  have hKernelPart : Q kernelPart = 0 := by
    dsimp [kernelPart]
    rw [map_sub, hIdempotent]
    abel
  have hFixedPart : Q fixedPart = fixedPart := by
    dsimp [fixedPart]
    exact hIdempotent f
  have hAnnihilatesApply (g : V) :
      continuousLinearMapFallingFactorialL2 T n g = 0 := by
    rw [hAnnihilates]
    rfl
  rw [← hDecompose, map_add]
  have hKernelZero :
      continuousLinearMapFallingFactorialL2 (Q + T) (n + 1) kernelPart = 0 := by
    rw [continuousLinearMapFallingFactorialL2_add_eq_of_left_eq_zero
          T Q hComm (n + 1) kernelPart hKernelPart,
      continuousLinearMapFallingFactorialL2_succ_apply,
      hAnnihilatesApply]
    simp
  have hFixedZero :
      continuousLinearMapFallingFactorialL2 (Q + T) (n + 1) fixedPart = 0 := by
    rw [continuousLinearMapFallingFactorialL2_add_succ_eq_shift_of_left_eq_self
          T Q hComm n fixedPart hFixedPart,
      hAnnihilatesApply]
    simp
  simpa [hKernelZero, hFixedZero]

/-- A finite sum of pairwise commuting idempotent continuous linear
endomorphisms is annihilated by

`X (X - 1) ... (X - card s)`.

This statement is purely algebraic and does not require finite-dimensionality. -/
theorem continuousLinearMapFallingFactorialL2_finset_sum_commuting_idempotents_eq_zero
    {ι : Type*}
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapFallingFactorialL2
        (Finset.sum s Q) s.card = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [continuousLinearMapFallingFactorialL2]
  | @insert a s ha ih =>
      have hCommSum : ∀ f : V,
          Q a ((Finset.sum s Q) f) =
            (Finset.sum s Q) (Q a f) := by
        intro f
        simp only [ContinuousLinearMap.sum_apply, map_sum]
        exact Finset.sum_congr rfl fun i hi => hComm a i f
      have hStep :=
        continuousLinearMapFallingFactorialL2_add_idempotent_succ_eq_zero
          (Finset.sum s Q) (Q a) hCommSum (hIdempotent a) s.card ih
      simpa [ha] using hStep

/-- The actual 324-link beta-zero heat-bath Hamiltonian satisfies the exact
operator polynomial identity

`H (H - I) ... (H - 324 I) = 0`.

Equivalently, `X (X - 1) ... (X - 324)` annihilates the native Gibbs `L²`
Hamiltonian. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_fallingFactorial_324_eq_zero :
    continuousLinearMapFallingFactorialL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
      324 = 0 := by
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  have hHamiltonian :
      C.heatBathHamiltonianL2 =
        ∑ edge : C.base.geometry.Edge,
          C.singleLinkHeatBathFluctuationL2 edge := by
    apply ContinuousLinearMap.ext
    intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathHamiltonianL2_eq_sum_commuting_fluctuation_family
        f
  rw [hHamiltonian]
  have hFamily :=
    continuousLinearMapFallingFactorialL2_finset_sum_commuting_idempotents_eq_zero
      (V := Lp ℝ 2 C.gibbsMeasure)
      (fun edge : C.base.geometry.Edge =>
        C.singleLinkHeatBathFluctuationL2 edge)
      Finset.univ
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    using hFamily

/-- Compact receipt for the first exact annihilating-polynomial identity of the
actual finite-volume beta-zero Hamiltonian. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCommutingIdempotentAnnihilatingPolynomialL2Receipt :
    Prop :=
  continuousLinearMapFallingFactorialL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
      324 = 0

/-- The actual beta-zero commuting-idempotent annihilating-polynomial receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCommutingIdempotentAnnihilatingPolynomialL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCommutingIdempotentAnnihilatingPolynomialL2Receipt := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_fallingFactorial_324_eq_zero

end

end MathlibAnalytic
end MGAP4D
