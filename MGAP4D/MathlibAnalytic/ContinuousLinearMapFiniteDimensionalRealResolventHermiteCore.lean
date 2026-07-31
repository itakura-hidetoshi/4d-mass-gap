import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventSpectralJetTransfer
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Ordered multiplication of a finite vector of continuous endomorphisms.
Unlike `Finset.prod`, this definition does not require commutativity. -/
def continuousLinearMapOrderedProduct
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (n : ℕ) → (Fin n → (V →L[ℝ] V)) → (V →L[ℝ] V)
  | 0, _ => 1
  | n + 1, R => R 0 * continuousLinearMapOrderedProduct n (fun i => R i.succ)

@[simp]
theorem continuousLinearMapOrderedProduct_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : Fin 0 → (V →L[ℝ] V)) :
    continuousLinearMapOrderedProduct 0 R = 1 := rfl

@[simp]
theorem continuousLinearMapOrderedProduct_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : Fin (n + 1) → (V →L[ℝ] V)) :
    continuousLinearMapOrderedProduct (n + 1) R =
      R 0 * continuousLinearMapOrderedProduct n (fun i => R i.succ) := rfl

/-- The ordered product of a constant vector is the corresponding power. -/
theorem continuousLinearMapOrderedProduct_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) :
    continuousLinearMapOrderedProduct n (fun _ => R) = R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [continuousLinearMapOrderedProduct_succ, ih]
      exact (pow_succ' R n).symm

/-- Ordered finite multiplication is continuous in the product supremum norm. -/
theorem continuous_continuousLinearMapOrderedProduct
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∀ n : ℕ,
      Continuous
        (continuousLinearMapOrderedProduct (V := V) n)
  | 0 => by
      simpa only [continuousLinearMapOrderedProduct] using
        (continuous_const : Continuous
          (fun _ : Fin 0 → (V →L[ℝ] V) => (1 : V →L[ℝ] V)))
  | n + 1 => by
      have htail : Continuous
          (fun R : Fin (n + 1) → (V →L[ℝ] V) =>
            fun i : Fin n => R i.succ) := by
        apply continuous_pi
        intro i
        exact continuous_apply i.succ
      exact (continuous_apply (0 : Fin (n + 1))).mul
        ((continuous_continuousLinearMapOrderedProduct n).comp htail)

/-- A common norm bound propagates through an ordered finite product. -/
theorem continuousLinearMapOrderedProduct_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : Fin n → (V →L[ℝ] V)) {M : ℝ}
    (hM : 0 ≤ M) (hR : ∀ i, ‖R i‖ ≤ M) :
    ‖continuousLinearMapOrderedProduct n R‖ ≤ M ^ n := by
  induction n with
  | zero =>
      change ‖ContinuousLinearMap.id ℝ V‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [continuousLinearMapOrderedProduct_succ]
      calc
        ‖R 0 * continuousLinearMapOrderedProduct n (fun i => R i.succ)‖ ≤
            ‖R 0‖ * ‖continuousLinearMapOrderedProduct n (fun i => R i.succ)‖ :=
          norm_mul_le _ _
        _ ≤ M * M ^ n := by
          exact mul_le_mul (hR 0)
            (ih (fun i => R i.succ) (fun i => hR i.succ))
            (norm_nonneg _) hM
        _ = M ^ (n + 1) := by
          rw [pow_succ']

/-- The normalized confluent divided-difference/Hermite observable of order
`order`.  For a tuple `(R₀, ..., Rₙ)` it is
`(-1)ⁿ R₀ ... Rₙ`, with the displayed order retained. -/
def continuousLinearMapRealResolventHermiteObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (R : Fin (order + 1) → (V →L[ℝ] V)) : V →L[ℝ] V :=
  (-1 : ℝ) ^ order •
    continuousLinearMapOrderedProduct (order + 1) R

/-- The finite vector of normalized Hermite observables through a fixed order,
all evaluated on the corresponding initial tuples. -/
def continuousLinearMapRealResolventHermiteJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (R : Fin (order + 1) → (V →L[ℝ] V)) :
    Fin (order + 1) → (V →L[ℝ] V) :=
  fun n => continuousLinearMapRealResolventHermiteObservable n.1
    (fun i => R ⟨i.1,
      Nat.lt_of_lt_of_le i.2
        (Nat.succ_le_succ (Nat.lt_succ_iff.mp n.2))⟩)

/-- Every fixed normalized Hermite observable is continuous. -/
theorem continuous_continuousLinearMapRealResolventHermiteObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) :
    Continuous
      (continuousLinearMapRealResolventHermiteObservable (V := V) order) := by
  unfold continuousLinearMapRealResolventHermiteObservable
  exact (continuous_const_smul ((-1 : ℝ) ^ order)).comp
    (continuous_continuousLinearMapOrderedProduct (order + 1))

/-- The finite Hermite jet is continuous in the product supremum norm. -/
theorem continuous_continuousLinearMapRealResolventHermiteJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) :
    Continuous
      (continuousLinearMapRealResolventHermiteJet (V := V) order) := by
  unfold continuousLinearMapRealResolventHermiteJet
  apply continuous_pi
  intro n
  apply (continuous_continuousLinearMapRealResolventHermiteObservable n.1).comp
  apply continuous_pi
  intro i
  exact continuous_apply
    (⟨i.1, Nat.lt_of_lt_of_le i.2
      (Nat.succ_le_succ (Nat.lt_succ_iff.mp n.2))⟩ : Fin (order + 1))

/-- Norm control for the normalized Hermite observable. -/
theorem continuousLinearMapRealResolventHermiteObservable_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (R : Fin (order + 1) → (V →L[ℝ] V)) {M : ℝ}
    (hM : 0 ≤ M) (hR : ∀ i, ‖R i‖ ≤ M) :
    ‖continuousLinearMapRealResolventHermiteObservable order R‖ ≤
      M ^ (order + 1) := by
  unfold continuousLinearMapRealResolventHermiteObservable
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact continuousLinearMapOrderedProduct_norm_le (order + 1) R hM hR

/-- The normalized Hermite coefficient of a true finite-dimensional real
resolvent at an ordered family of spectral nodes. -/
def continuousLinearMapRealResolventHermiteCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (order : ℕ) (A : V →L[ℝ] V) (nodes : Fin (order + 1) → ℝ) :
    V →L[ℝ] V :=
  continuousLinearMapRealResolventHermiteObservable order
    (fun i => continuousLinearMapRealResolvent A (nodes i))

/-- On the full diagonal, the normalized Hermite coefficient is the signed
resolvent power. -/
theorem continuousLinearMapRealResolventHermiteObservable_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (R : V →L[ℝ] V) :
    continuousLinearMapRealResolventHermiteObservable order (fun _ => R) =
      (-1 : ℝ) ^ order • R ^ (order + 1) := by
  unfold continuousLinearMapRealResolventHermiteObservable
  rw [continuousLinearMapOrderedProduct_const]

/-- Multiplication by `order!` identifies the diagonal Hermite coefficient
with the algebraic spectral jet. -/
theorem factorial_smul_continuousLinearMapRealResolventHermiteObservable_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (R : V →L[ℝ] V) :
    (order.factorial : ℝ) •
        continuousLinearMapRealResolventHermiteObservable order (fun _ => R) =
      continuousLinearMapRealResolventSpectralJet order R := by
  rw [continuousLinearMapRealResolventHermiteObservable_const]
  unfold continuousLinearMapRealResolventSpectralJet
  rw [smul_smul]
  congr 1
  simp [continuousLinearMapRealResolventSpectralCoefficient]
  ring

/-- The full-diagonal Hermite coefficient of a true resolvent is the spectral
jet divided by the factorial, expressed without division. -/
theorem factorial_smul_continuousLinearMapRealResolventHermiteCoefficient_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (order : ℕ) (A : V →L[ℝ] V) (z : ℝ) :
    (order.factorial : ℝ) •
        continuousLinearMapRealResolventHermiteCoefficient order A (fun _ => z) =
      continuousLinearMapRealResolventSpectralJet order
        (continuousLinearMapRealResolvent A z) := by
  exact factorial_smul_continuousLinearMapRealResolventHermiteObservable_const
    order (continuousLinearMapRealResolvent A z)

/-- On an open common resolvent region, the diagonal Hermite coefficient is
exactly the true iterated spectral derivative after multiplication by the
factorial. -/
theorem factorial_smul_continuousLinearMapRealResolventHermiteCoefficient_const_eq_iteratedDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (order : ℕ) {z : ℝ} (hz : z ∈ U) :
    (order.factorial : ℝ) •
        continuousLinearMapRealResolventHermiteCoefficient order A (fun _ => z) =
      iteratedDeriv order (continuousLinearMapRealResolvent A) z := by
  rw [factorial_smul_continuousLinearMapRealResolventHermiteCoefficient_const]
  exact continuousLinearMapRealResolventSpectralJet_eq_iteratedDeriv
    A U M hU hM hunit hnorm order hz

/-- The order-one normalized Hermite coefficient satisfies the defining
first divided-difference identity, including the confluent case. -/
theorem continuousLinearMapRealResolventHermiteCoefficient_one_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) {z w : ℝ}
    (hz : IsUnit (continuousLinearMapRealShift A z))
    (hw : IsUnit (continuousLinearMapRealShift A w)) :
    (z - w) •
        continuousLinearMapRealResolventHermiteCoefficient 1 A
          (Fin.cases z (fun _ => w)) =
      continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w := by
  rw [continuousLinearMapRealResolvent_sub_eq_smul_mul A hz hw]
  have hnode : (Fin.cases z (fun _ => w)) (1 : Fin 2) = w := by
    rfl
  have hcoeff :
      continuousLinearMapRealResolventHermiteCoefficient 1 A
          (Fin.cases z (fun _ => w)) =
        (-1 : ℝ) •
          (continuousLinearMapRealResolvent A z *
            continuousLinearMapRealResolvent A w) := by
    simp [continuousLinearMapRealResolventHermiteCoefficient,
      continuousLinearMapRealResolventHermiteObservable,
      continuousLinearMapOrderedProduct, hnode]
  rw [hcoeff, smul_smul]
  congr 1
  ring

end MathlibAnalytic
end MGAP4D
