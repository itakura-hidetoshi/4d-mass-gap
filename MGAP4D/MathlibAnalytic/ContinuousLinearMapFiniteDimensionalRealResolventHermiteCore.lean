import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventSpectralJetTransfer
import Mathlib.Data.Fin.VecNotation
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

/-- The ordered product can also be split at its last factor. -/
theorem continuousLinearMapOrderedProduct_snoc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : Fin (n + 1) → (V →L[ℝ] V)) :
    continuousLinearMapOrderedProduct (n + 1) R =
      continuousLinearMapOrderedProduct n (Fin.init R) * R (Fin.last n) := by
  induction n with
  | zero =>
      simp [continuousLinearMapOrderedProduct]
  | succ n ih =>
      rw [continuousLinearMapOrderedProduct_succ]
      change R 0 * continuousLinearMapOrderedProduct (n + 1) (Fin.tail R) =
        continuousLinearMapOrderedProduct (n + 1) (Fin.init R) *
          R (Fin.last (n + 1))
      rw [ih (Fin.tail R), continuousLinearMapOrderedProduct_succ]
      have hmiddle : Fin.init (Fin.tail R) = fun i => R i.castSucc.succ := by
        funext i
        rfl
      rw [hmiddle]

/-- An endomorphism commuting with every factor commutes with their ordered
finite product. -/
theorem continuousLinearMap_mul_orderedProduct_eq_orderedProduct_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) (R : Fin n → (V →L[ℝ] V))
    (hcomm : ∀ i, A * R i = R i * A) :
    A * continuousLinearMapOrderedProduct n R =
      continuousLinearMapOrderedProduct n R * A := by
  induction n with
  | zero => simp [continuousLinearMapOrderedProduct]
  | succ n ih =>
      rw [continuousLinearMapOrderedProduct_succ]
      calc
        A * (R 0 * continuousLinearMapOrderedProduct n (fun i => R i.succ)) =
            (A * R 0) * continuousLinearMapOrderedProduct n (fun i => R i.succ) :=
          (mul_assoc _ _ _).symm
        _ = (R 0 * A) * continuousLinearMapOrderedProduct n (fun i => R i.succ) := by
          rw [hcomm 0]
        _ = R 0 * (A * continuousLinearMapOrderedProduct n (fun i => R i.succ)) :=
          mul_assoc _ _ _
        _ = R 0 * (continuousLinearMapOrderedProduct n (fun i => R i.succ) * A) := by
          rw [ih (fun i => R i.succ) (fun i => hcomm i.succ)]
        _ = (R 0 * continuousLinearMapOrderedProduct n (fun i => R i.succ)) * A :=
          (mul_assoc _ _ _).symm

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

/-- Real resolvents of the same finite-dimensional endomorphism commute at
any two points of their common resolvent set. -/
theorem continuousLinearMapRealResolvent_commute
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) {z w : ℝ}
    (hz : IsUnit (continuousLinearMapRealShift A z))
    (hw : IsUnit (continuousLinearMapRealShift A w)) :
    continuousLinearMapRealResolvent A z * continuousLinearMapRealResolvent A w =
      continuousLinearMapRealResolvent A w * continuousLinearMapRealResolvent A z := by
  by_cases hzw : w = z
  · subst w
    rfl
  · have hne : w - z ≠ 0 := sub_ne_zero.mpr hzw
    have hforward := continuousLinearMapRealResolvent_sub_eq_smul_mul A hz hw
    have hbackward := continuousLinearMapRealResolvent_sub_eq_smul_mul A hw hz
    have hbackward' :
        continuousLinearMapRealResolvent A z - continuousLinearMapRealResolvent A w =
          (w - z) • (continuousLinearMapRealResolvent A w *
            continuousLinearMapRealResolvent A z) := by
      calc
        continuousLinearMapRealResolvent A z - continuousLinearMapRealResolvent A w =
            -(continuousLinearMapRealResolvent A w -
              continuousLinearMapRealResolvent A z) := by abel
        _ = -((z - w) • (continuousLinearMapRealResolvent A w *
              continuousLinearMapRealResolvent A z)) := by rw [hbackward]
        _ = (w - z) • (continuousLinearMapRealResolvent A w *
              continuousLinearMapRealResolvent A z) := by module
    calc
      continuousLinearMapRealResolvent A z * continuousLinearMapRealResolvent A w =
          (w - z)⁻¹ • ((w - z) •
            (continuousLinearMapRealResolvent A z *
              continuousLinearMapRealResolvent A w)) :=
        (inv_smul_smul₀ hne _).symm
      _ = (w - z)⁻¹ •
          (continuousLinearMapRealResolvent A z -
            continuousLinearMapRealResolvent A w) := by rw [hforward]
      _ = (w - z)⁻¹ • ((w - z) •
          (continuousLinearMapRealResolvent A w *
            continuousLinearMapRealResolvent A z)) := by rw [hbackward']
      _ = continuousLinearMapRealResolvent A w *
          continuousLinearMapRealResolvent A z := inv_smul_smul₀ hne _

/-- The normalized multipoint coefficient satisfies the full divided-difference
recursion. Repeated endpoints are allowed; no division by their difference is
used. -/
theorem continuousLinearMapRealResolventHermiteCoefficient_succ_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) (nodes : Fin (n + 2) → ℝ)
    (hunit : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i))) :
    (nodes 0 - nodes (Fin.last (n + 1))) •
        continuousLinearMapRealResolventHermiteCoefficient (n + 1) A nodes =
      continuousLinearMapRealResolventHermiteCoefficient n A (Fin.init nodes) -
        continuousLinearMapRealResolventHermiteCoefficient n A (Fin.tail nodes) := by
  let R : Fin (n + 2) → (V →L[ℝ] V) :=
    fun i => continuousLinearMapRealResolvent A (nodes i)
  let P : V →L[ℝ] V :=
    continuousLinearMapOrderedProduct n (Fin.init (Fin.tail R))
  have hlastP : R (Fin.last (n + 1)) * P = P * R (Fin.last (n + 1)) := by
    apply continuousLinearMap_mul_orderedProduct_eq_orderedProduct_mul
    intro i
    simpa [R, Fin.init, Fin.tail] using
      continuousLinearMapRealResolvent_commute A
        (hunit (Fin.last (n + 1))) (hunit i.castSucc.succ)
  have hinit :
      continuousLinearMapOrderedProduct (n + 1) (Fin.init R) = R 0 * P := by
    rw [continuousLinearMapOrderedProduct_succ]
    change R 0 * continuousLinearMapOrderedProduct n (Fin.tail (Fin.init R)) =
      R 0 * P
    rw [Fin.tail_init_eq_init_tail]
  have htail :
      continuousLinearMapOrderedProduct (n + 1) (Fin.tail R) =
        P * R (Fin.last (n + 1)) := by
    simpa [P, Fin.init, Fin.tail] using
      continuousLinearMapOrderedProduct_snoc n (Fin.tail R)
  have hfull :
      continuousLinearMapOrderedProduct (n + 2) R =
        R 0 * (P * R (Fin.last (n + 1))) := by
    rw [continuousLinearMapOrderedProduct_succ]
    change R 0 * continuousLinearMapOrderedProduct (n + 1) (Fin.tail R) =
      R 0 * (P * R (Fin.last (n + 1)))
    rw [htail]
  have hdiff :
      R 0 - R (Fin.last (n + 1)) =
        (nodes (Fin.last (n + 1)) - nodes 0) •
          (R 0 * R (Fin.last (n + 1))) := by
    simpa [R] using continuousLinearMapRealResolvent_sub_eq_smul_mul A
      (hunit 0) (hunit (Fin.last (n + 1)))
  have hprodDiff :
      continuousLinearMapOrderedProduct (n + 1) (Fin.init R) -
          continuousLinearMapOrderedProduct (n + 1) (Fin.tail R) =
        (nodes (Fin.last (n + 1)) - nodes 0) •
          continuousLinearMapOrderedProduct (n + 2) R := by
    rw [hinit, htail, hfull]
    calc
      R 0 * P - P * R (Fin.last (n + 1)) =
          R 0 * P - R (Fin.last (n + 1)) * P := by
        rw [hlastP]
      _ = (R 0 - R (Fin.last (n + 1))) * P := by
        rw [sub_mul]
      _ = ((nodes (Fin.last (n + 1)) - nodes 0) •
          (R 0 * R (Fin.last (n + 1)))) * P := by
        rw [hdiff]
      _ = (nodes (Fin.last (n + 1)) - nodes 0) •
          ((R 0 * R (Fin.last (n + 1))) * P) := by
        rw [smul_mul_assoc]
      _ = (nodes (Fin.last (n + 1)) - nodes 0) •
          (R 0 * (P * R (Fin.last (n + 1)))) := by
        rw [mul_assoc, hlastP]
  change (nodes 0 - nodes (Fin.last (n + 1))) •
      continuousLinearMapRealResolventHermiteObservable (n + 1) R =
    continuousLinearMapRealResolventHermiteObservable n (Fin.init R) -
      continuousLinearMapRealResolventHermiteObservable n (Fin.tail R)
  unfold continuousLinearMapRealResolventHermiteObservable
  rw [← smul_sub, hprodDiff, smul_smul, smul_smul]
  congr 1
  rw [pow_succ]
  ring

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
        continuousLinearMapRealResolventHermiteCoefficient 1 A ![z, w] =
      continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w := by
  rw [continuousLinearMapRealResolvent_sub_eq_smul_mul A hz hw]
  have hcoeff :
      continuousLinearMapRealResolventHermiteCoefficient 1 A ![z, w] =
        (-1 : ℝ) •
          (continuousLinearMapRealResolvent A z *
            continuousLinearMapRealResolvent A w) := by
    simp [continuousLinearMapRealResolventHermiteCoefficient,
      continuousLinearMapRealResolventHermiteObservable,
      continuousLinearMapOrderedProduct]
  rw [hcoeff, smul_smul]
  congr 1
  ring

end MathlibAnalytic
end MGAP4D
