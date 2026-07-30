import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventSecondDerivativeBundle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- The `k`-th composition power of the orthonormal-diagonal resolvent has
within-derivative `k • R^(k+1)` throughout the open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_pow_hasDerivWithinAt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < delta) :
    HasDerivWithinAt
      (fun mu => (orthonormalDiagonalHamiltonianResolvent b a mu) ^ k)
      ((k : ℝ) •
        (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (k + 1))
      (Set.Iio delta) lambda := by
  induction k with
  | zero =>
      have hconst :
          HasDerivWithinAt
            (fun _ : ℝ => (1 : E →L[ℝ] E))
            (0 : E →L[ℝ] E)
            (Set.Iio delta) lambda :=
        hasDerivWithinAt_const lambda (Set.Iio delta) (1 : E →L[ℝ] E)
      have hzero :
          (((0 : ℕ) : ℝ) •
              (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (0 + 1)) =
            (0 : E →L[ℝ] E) := by
        rw [Nat.cast_zero]
        exact zero_smul ℝ
          ((orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (0 + 1))
      rw [hzero]
      simpa only [pow_zero] using hconst
  | succ k ih =>
      have hR :
          HasDerivWithinAt
            (orthonormalDiagonalHamiltonianResolvent b a)
            ((orthonormalDiagonalHamiltonianResolvent b a lambda) ^ 2)
            (Set.Iio delta) lambda := by
        simpa [pow_two, ContinuousLinearMap.mul_def] using
          (orthonormalDiagonalHamiltonianResolvent_hasDerivWithinAt
            b a delta hdelta hlambda)
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ) (𝔸 := E →L[ℝ] E) ih hR
      have hmul' :
          HasDerivWithinAt
            (fun mu =>
              (orthonormalDiagonalHamiltonianResolvent b a mu) ^ (k + 1))
            ((k : ℝ) •
                (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (k + 1) *
                  orthonormalDiagonalHamiltonianResolvent b a lambda +
              (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k *
                (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ 2)
            (Set.Iio delta) lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((k : ℝ) •
                (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (k + 1) *
                  orthonormalDiagonalHamiltonianResolvent b a lambda +
              (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k *
                (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ 2) =
            ((Nat.succ k : ℕ) : ℝ) •
              (orthonormalDiagonalHamiltonianResolvent b a lambda) ^
                (Nat.succ k + 1) := by
        let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
        change
          ((k : ℝ) • Rlambda ^ (k + 1)) * Rlambda +
              Rlambda ^ k * Rlambda ^ 2 =
            ((Nat.succ k : ℕ) : ℝ) • Rlambda ^ (Nat.succ k + 1)
        have hsmul :
            ((k : ℝ) • Rlambda ^ (k + 1)) * Rlambda =
              (k : ℝ) • (Rlambda ^ (k + 1) * Rlambda) :=
          Algebra.smul_mul_assoc (k : ℝ) (Rlambda ^ (k + 1)) Rlambda
        rw [hsmul]
        have hfirst : Rlambda ^ (k + 1) * Rlambda = Rlambda ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ Rlambda (k + 1)).symm
        have hsecond : Rlambda ^ k * Rlambda ^ 2 = Rlambda ^ (k + 2) := by
          simpa using (pow_add Rlambda k 2).symm
        rw [hfirst, hsecond]
        calc
          (k : ℝ) • Rlambda ^ (k + 2) + Rlambda ^ (k + 2) =
              (k : ℝ) • Rlambda ^ (k + 2) +
                (1 : ℝ) • Rlambda ^ (k + 2) := by
            rw [one_smul ℝ]
          _ = ((k : ℝ) + 1) • Rlambda ^ (k + 2) :=
            (add_smul (k : ℝ) (1 : ℝ) (Rlambda ^ (k + 2))).symm
          _ = ((Nat.succ k : ℕ) : ℝ) •
              Rlambda ^ (Nat.succ k + 1) := by
            rw [Nat.cast_succ]
      rw [hderiv] at hmul'
      exact hmul'

/-- The orthonormal-diagonal resolvent is `Cⁿ` in operator norm for every
finite order on the open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_contDiffOn_nat
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (n : ℕ) :
    ContDiffOn ℝ n
      (orthonormalDiagonalHamiltonianResolvent b a)
      (Set.Iio delta) := by
  induction n with
  | zero =>
      change ContDiffOn ℝ 0
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta)
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (orthonormalDiagonalHamiltonianResolvent_continuousOn
          b a delta hdelta)
  | succ n ih =>
      apply (contDiffOn_succ_iff_deriv_of_isOpen
        (n := (n : ℕ∞ω)) isOpen_Iio).2
      refine ⟨orthonormalDiagonalHamiltonianResolvent_differentiableOn
        b a delta hdelta, ?_, ?_⟩
      · simp
      · have hsquare :
            ContDiffOn ℝ n
              (fun lambda =>
                (orthonormalDiagonalHamiltonianResolvent b a lambda).comp
                  (orthonormalDiagonalHamiltonianResolvent b a lambda))
              (Set.Iio delta) :=
          ih.clm_comp ih
        apply hsquare.congr
        intro lambda hlambda
        exact orthonormalDiagonalHamiltonianResolvent_deriv
          b a delta hdelta hlambda

/-- The orthonormal-diagonal resolvent is smooth in operator norm throughout
the complete open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_contDiffOn_infty
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ ∞
      (orthonormalDiagonalHamiltonianResolvent b a)
      (Set.Iio delta) :=
  contDiffOn_infty.2 fun n =>
    orthonormalDiagonalHamiltonianResolvent_contDiffOn_nat
      b a delta hdelta n

/-- Finite-order and smooth regularity package for the generic resolvent. -/
theorem orthonormalDiagonalHamiltonianResolventSmoothness_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ ∞
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) ∧
      ∀ n : ℕ,
        ContDiffOn ℝ n
          (orthonormalDiagonalHamiltonianResolvent b a)
          (Set.Iio delta) :=
  ⟨orthonormalDiagonalHamiltonianResolvent_contDiffOn_infty
      b a delta hdelta,
    fun n => orthonormalDiagonalHamiltonianResolvent_contDiffOn_nat
      b a delta hdelta n⟩

/-- Every iterated derivative within the open sub-gap interval is the factorial
multiple of the corresponding resolvent composition power. -/
theorem orthonormalDiagonalHamiltonianResolvent_iteratedDerivWithin
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < delta) :
    iteratedDerivWithin n
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) lambda =
      (n.factorial : ℝ) •
        (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (orthonormalDiagonalHamiltonianResolvent b a)
                (Set.Iio delta))
              (Set.Iio delta) lambda =
            derivWithin
              (fun mu =>
                (n.factorial : ℝ) •
                  (orthonormalDiagonalHamiltonianResolvent b a mu) ^ (n + 1))
              (Set.Iio delta) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hpow :=
        orthonormalDiagonalHamiltonianResolvent_pow_hasDerivWithinAt
          b a delta hdelta (n + 1) hlambda
      have hscaled :
          HasDerivWithinAt
            (fun mu =>
              (n.factorial : ℝ) •
                (orthonormalDiagonalHamiltonianResolvent b a mu) ^ (n + 1))
            ((n.factorial : ℝ) •
              (((n + 1 : ℕ) : ℝ) •
                (orthonormalDiagonalHamiltonianResolvent b a lambda) ^
                  (n + 2)))
            (Set.Iio delta) lambda := by
        simpa only [Pi.smul_apply] using
          (HasDerivWithinAt.const_smul
            (𝕜 := ℝ) (R := ℝ) (F := E →L[ℝ] E)
            (n.factorial : ℝ) hpow)
      let derivValue : E →L[ℝ] E :=
        (n.factorial : ℝ) •
          (((n + 1 : ℕ) : ℝ) •
            (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (n + 2))
      have hfscaled :
          HasFDerivWithinAt
            (fun mu =>
              (n.factorial : ℝ) •
                (orthonormalDiagonalHamiltonianResolvent b a mu) ^ (n + 1))
            (toSpanSingleton ℝ derivValue)
            (Set.Iio delta) lambda := by
        simpa [derivValue] using hscaled.hasFDerivWithinAt
      have hfderiv :
          fderivWithin ℝ
              (fun mu =>
                (n.factorial : ℝ) •
                  (orthonormalDiagonalHamiltonianResolvent b a mu) ^ (n + 1))
              (Set.Iio delta) lambda =
            toSpanSingleton ℝ derivValue :=
        hfscaled.fderivWithin (isOpen_Iio.uniqueDiffOn lambda hlambda)
      have hscaledDeriv :
          derivWithin
              (fun mu =>
                (n.factorial : ℝ) •
                  (orthonormalDiagonalHamiltonianResolvent b a mu) ^ (n + 1))
              (Set.Iio delta) lambda = derivValue := by
        unfold derivWithin
        rw [hfderiv]
        simp [derivValue]
      rw [hscaledDeriv]
      simp [derivValue, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        smul_smul, mul_comm, Nat.add_assoc]

/-- Explicit ordinary all-order derivative formula below the spectral gap:
`R^(n)(lambda) = n! • R(lambda)^(n+1)`. -/
theorem orthonormalDiagonalHamiltonianResolvent_iteratedDeriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < delta) :
    iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda =
      (n.factorial : ℝ) •
        (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (n + 1) := by
  calc
    iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda =
      iteratedDerivWithin n
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := orthonormalDiagonalHamiltonianResolvent b a)
        isOpen_Iio hlambda).symm
    _ = (n.factorial : ℝ) •
        (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (n + 1) :=
      orthonormalDiagonalHamiltonianResolvent_iteratedDerivWithin
        b a delta hdelta n hlambda

/-- Every operator-norm derivative of the orthonormal-diagonal resolvent has
the exact factorial Cauchy-type distance-to-gap bound. -/
theorem orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < delta) :
    ‖iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ ≤
      (n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1) := by
  rw [orthonormalDiagonalHamiltonianResolvent_iteratedDeriv
    b a delta hdelta n hlambda]
  let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
  change ‖(n.factorial : ℝ) • Rlambda ^ (n + 1)‖ ≤
    (n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1)
  calc
    ‖(n.factorial : ℝ) • Rlambda ^ (n + 1)‖ ≤
        ‖(n.factorial : ℝ)‖ * ‖Rlambda ^ (n + 1)‖ :=
      ContinuousLinearMap.opNorm_smul_le
        (n.factorial : ℝ) (Rlambda ^ (n + 1))
    _ = (n.factorial : ℝ) * ‖Rlambda ^ (n + 1)‖ := by
      rw [Real.norm_natCast]
    _ ≤ (n.factorial : ℝ) * ‖Rlambda‖ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (norm_pow_le' Rlambda (by omega)) (by positivity)
    _ ≤ (n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg Rlambda)
          (orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
            b a delta lambda hdelta hlambda)
          (n + 1))
        (by positivity)

/-- Uniform factorial derivative bound on every truncation that stays at least
`epsilon` below the spectral gap. -/
theorem orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le_of_le_sub
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (n : ℕ) {epsilon lambda : ℝ} (hepsilon : 0 < epsilon)
    (hlambda : lambda < delta) (haway : lambda ≤ delta - epsilon) :
    ‖iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ ≤
      (n.factorial : ℝ) * (epsilon⁻¹) ^ (n + 1) := by
  have hdist : epsilon ≤ delta - lambda := by
    linarith
  have hinv : (delta - lambda)⁻¹ ≤ epsilon⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hepsilon hdist
  calc
    ‖iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ ≤
      (n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1) :=
        orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le
          b a delta hdelta n hlambda
    _ ≤ (n.factorial : ℝ) * (epsilon⁻¹) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)) hinv (n + 1))
        (by positivity)

/-- Pointwise form of the factorial derivative bound on every state vector. -/
theorem orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_apply_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < delta) (x : E) :
    ‖(iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda) x‖ ≤
      ((n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1)) * ‖x‖ := by
  calc
    ‖(iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda) x‖ ≤
        ‖iteratedDeriv n
          (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ * ‖x‖ :=
      (iteratedDeriv n
        (orthonormalDiagonalHamiltonianResolvent b a) lambda).le_opNorm x
    _ ≤ ((n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le
          b a delta hdelta n hlambda)
        (norm_nonneg x)

/-- Smoothness, exact all-order derivatives, and factorial operator-norm bounds
for the orthonormal-diagonal resolvent. -/
theorem orthonormalDiagonalHamiltonianResolventFactorialDerivative_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ContDiffOn ℝ ∞
        (orthonormalDiagonalHamiltonianResolvent b a)
        (Set.Iio delta) ∧
      (∀ (n : ℕ) {lambda : ℝ} (hlambda : lambda < delta),
        iteratedDeriv n
            (orthonormalDiagonalHamiltonianResolvent b a) lambda =
          (n.factorial : ℝ) •
            (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (n + 1)) ∧
      ∀ (n : ℕ) {lambda : ℝ} (_ : lambda < delta),
        ‖iteratedDeriv n
            (orthonormalDiagonalHamiltonianResolvent b a) lambda‖ ≤
          (n.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (n + 1) := by
  refine ⟨orthonormalDiagonalHamiltonianResolvent_contDiffOn_infty
      b a delta hdelta, ?_, ?_⟩
  · intro n lambda hlambda
    exact orthonormalDiagonalHamiltonianResolvent_iteratedDeriv
      b a delta hdelta n (lambda := lambda) hlambda
  · intro n lambda hlambda
    exact orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le
      b a delta hdelta n (lambda := lambda) hlambda

end MathlibAnalytic
end MGAP4D

end
