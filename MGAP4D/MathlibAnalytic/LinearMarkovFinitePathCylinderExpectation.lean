import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPMF
import MGAP4D.MathlibAnalytic.LinearMarkovCylinderMoment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Finite-PMF real expectation commutes with multiplication by a real constant. -/
theorem finite_pmfExpectationReal_const_mul
    {α : Type*} [Fintype α]
    (p : PMF α)
    (c : ℝ)
    (f : α → ℝ) :
    finitePMFExpectationReal p (fun a => c * f a) =
      c * finitePMFExpectationReal p f := by
  classical
  unfold finitePMFExpectationReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- The real expectation of the constant-one observable under a finite PMF is
one. -/
theorem finite_pmfExpectationReal_one
    {α : Type*} [Fintype α]
    (p : PMF α) :
    finitePMFExpectationReal p (fun _ : α => (1 : ℝ)) = 1 := by
  classical
  unfold finitePMFExpectationReal
  simp only [mul_one]
  have hsum : ∑ a : α, p a = 1 := by
    simpa [tsum_fintype] using PMF.tsum_coe p
  calc
    ∑ a : α, (p a).toReal = (∑ a : α, p a).toReal := by
      symm
      rw [ENNReal.toReal_sum]
      intro a _ha
      exact p.apply_ne_top a
    _ = 1 := by rw [hsum]; simp

/-- The real expectation operator associated with a finite-state transition
PMF, bundled as a real-linear map on observables. -/
def finitePMFTransitionExpectationLinearMap
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω) :
    (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun f x := finitePMFExpectationReal (transition x) f
  map_add' f g := by
    classical
    funext x
    unfold finitePMFExpectationReal
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  map_smul' c f := by
    classical
    funext x
    unfold finitePMFExpectationReal
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring

@[simp] theorem finitePMFTransitionExpectationLinearMap_apply
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (f : Ω → ℝ)
    (x : Ω) :
    finitePMFTransitionExpectationLinearMap transition f x =
      finitePMFExpectationReal (transition x) f :=
  rfl

/-- Every finite-state transition-PMF expectation operator preserves the
constant-one observable. -/
theorem finitePMFTransitionExpectationLinearMap_one
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω) :
    finitePMFTransitionExpectationLinearMap transition
        (fun _ : Ω => (1 : ℝ)) =
      fun _ => 1 := by
  funext x
  exact finite_pmfExpectationReal_one (transition x)

/-- Product of the observables on the first `n` coordinates of an
`n + 1`-coordinate path, followed by a separate terminal observable. -/
def linearMarkovFinitePathCylinderProduct
    {Ω : Type*}
    (n : ℕ)
    (fs : Fin n → Ω → ℝ)
    (h : Ω → ℝ)
    (path : Fin (n + 1) → Ω) : ℝ :=
  (∏ i : Fin n, fs i (path i.castSucc)) *
    h (path (Fin.last n))

/-- Appending one transition and integrating its new terminal coordinate
contracts the final two factors by the transition expectation operator. -/
theorem linearMarkovFinitePathCylinderProduct_snoc_expectation
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ)
    (h : Ω → ℝ)
    (path : Fin (n + 1) → Ω) :
    finitePMFExpectationReal (transition (path (Fin.last n)))
        (fun y =>
          linearMarkovFinitePathCylinderProduct (n + 1) fs h
            (Fin.snoc path y)) =
      linearMarkovFinitePathCylinderProduct n
        (Fin.init fs)
        (fun x =>
          fs (Fin.last n) x *
            finitePMFExpectationReal (transition x) h)
        path := by
  classical
  unfold linearMarkovFinitePathCylinderProduct
  simp_rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init_def]
  rw [finite_pmfExpectationReal_const_mul]
  ring

/-- In backward cylinder conditioning, the final pair `[g, h]` contracts to the
single terminal observable `g * P h` when the transition preserves one. -/
theorem linearMarkovCylinderCondition_append_pair_contract
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (fs : List (Ω → ℝ))
    (g h : Ω → ℝ) :
    linearMarkovCylinderCondition P (fs ++ [g, h]) =
      linearMarkovCylinderCondition P
        (fs ++ [fun x => g x * P h x]) := by
  induction fs with
  | nil =>
      funext x
      simp [linearMarkovCylinderCondition, hPone]
  | cons f fs ih =>
      funext x
      simp only [List.cons_append, linearMarkovCylinderCondition_cons]
      rw [ih]

/-- The corresponding terminal-pair contraction identity for finite-cylinder
moments. -/
theorem linearMarkovCylinderMoment_append_pair_contract
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (fs : List (Ω → ℝ))
    (g h : Ω → ℝ) :
    linearMarkovCylinderMoment state P (fs ++ [g, h]) =
      linearMarkovCylinderMoment state P
        (fs ++ [fun x => g x * P h x]) := by
  unfold linearMarkovCylinderMoment
  rw [linearMarkovCylinderCondition_append_pair_contract P hPone fs g h]

/-- The product expectation under the honest finite Markov path PMF equals the
existing backward cylinder-moment recursion, with the last observable separated
from the preceding `n` observables. -/
theorem linearMarkovFinitePathPMF_terminalCylinder_expectation
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin n → Ω → ℝ)
    (h : Ω → ℝ) :
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (linearMarkovFinitePathCylinderProduct n fs h) =
      linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs ++ [h]) := by
  induction n generalizing h with
  | zero =>
      have hfs : List.ofFn fs = [] := by simp
      rw [linearMarkovFinitePathPMF, finite_pmfExpectationReal_map,
        hfs, List.nil_append]
      rw [linearMarkovCylinderMoment_singleton
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (finitePMFTransitionExpectationLinearMap_one transition)]
      simp [linearMarkovFinitePathCylinderProduct]
  | succ n ih =>
      rw [linearMarkovFinitePathPMF, finite_pmfExpectationReal_bind]
      simp_rw [finite_pmfExpectationReal_map]
      simp_rw [linearMarkovFinitePathCylinderProduct_snoc_expectation]
      rw [ih (Fin.init fs)
        (fun x =>
          fs (Fin.last n) x *
            finitePMFExpectationReal (transition x) h)]
      calc
        linearMarkovCylinderMoment
            (finitePMFExpectationReal initial)
            (finitePMFTransitionExpectationLinearMap transition)
            (List.ofFn (Fin.init fs) ++
              [fun x =>
                fs (Fin.last n) x *
                  finitePMFExpectationReal (transition x) h]) =
          linearMarkovCylinderMoment
            (finitePMFExpectationReal initial)
            (finitePMFTransitionExpectationLinearMap transition)
            (List.ofFn (Fin.init fs) ++ [fs (Fin.last n), h]) := by
              symm
              simpa using
                linearMarkovCylinderMoment_append_pair_contract
                  (finitePMFExpectationReal initial)
                  (finitePMFTransitionExpectationLinearMap transition)
                  (finitePMFTransitionExpectationLinearMap_one transition)
                  (List.ofFn (Fin.init fs))
                  (fs (Fin.last n)) h
        _ = linearMarkovCylinderMoment
            (finitePMFExpectationReal initial)
            (finitePMFTransitionExpectationLinearMap transition)
            (List.ofFn fs ++ [h]) := by
              rw [List.ofFn_succ_last]
              simp only [Fin.init_def, List.append_assoc]

/-- For every finite tuple of observables, its product expectation under the
honest finite path PMF is exactly the pre-existing cylinder moment. -/
theorem linearMarkovFinitePathPMF_cylinderProduct_expectation
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ) :
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (fun path => ∏ i : Fin (n + 1), fs i (path i)) =
      linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs) := by
  have h :=
    linearMarkovFinitePathPMF_terminalCylinder_expectation
      initial transition n (Fin.init fs) (fs (Fin.last n))
  calc
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (fun path => ∏ i : Fin (n + 1), fs i (path i)) =
      finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (linearMarkovFinitePathCylinderProduct n
          (Fin.init fs) (fs (Fin.last n))) := by
            congr 1
            funext path
            unfold linearMarkovFinitePathCylinderProduct
            rw [Fin.prod_univ_castSucc]
            simp only [Fin.init_def]
    _ = linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn (Fin.init fs) ++ [fs (Fin.last n)]) := h
    _ = linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs) := by
          rw [List.ofFn_succ_last]
          simp only [Fin.init_def]

end

end MathlibAnalytic
end MGAP4D
