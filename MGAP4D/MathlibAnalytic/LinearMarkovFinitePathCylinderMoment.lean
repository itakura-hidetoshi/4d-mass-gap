import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPMF
import MGAP4D.MathlibAnalytic.LinearMarkovCylinderMoment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The real expectation operator associated with a finite-state transition PMF,
bundled as a real-linear map on observables. -/
def finitePMFTransitionExpectationLinearMap
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω) :
    (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun f x := finitePMFExpectationReal (transition x) f
  map_add' f g := by
    classical
    funext x
    unfold finitePMFExpectationReal
    calc
      ∑ y : Ω, ((transition x y).toReal * (f y + g y)) =
          ∑ y : Ω,
            ((transition x y).toReal * f y +
              (transition x y).toReal * g y) := by
            apply Finset.sum_congr rfl
            intro y _hy
            ring
      _ =
          (∑ y : Ω, (transition x y).toReal * f y) +
            ∑ y : Ω, (transition x y).toReal * g y := by
              rw [Finset.sum_add_distrib]
  map_smul' c f := by
    classical
    funext x
    unfold finitePMFExpectationReal
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      ∑ y : Ω, (transition x y).toReal * (c * f y) =
          ∑ y : Ω, c * ((transition x y).toReal * f y) := by
            apply Finset.sum_congr rfl
            intro y _hy
            ring
      _ = c * ∑ y : Ω, (transition x y).toReal * f y := by
        rw [Finset.mul_sum]

/-- A transition PMF preserves the constant-one observable in real
expectation. -/
theorem finitePMFTransitionExpectationLinearMap_one
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω) :
    finitePMFTransitionExpectationLinearMap transition
        (fun _ : Ω => (1 : ℝ)) =
      fun _ : Ω => 1 := by
  classical
  funext x
  change finitePMFExpectationReal (transition x)
      (fun _ : Ω => (1 : ℝ)) = 1
  unfold finitePMFExpectationReal
  simp only [mul_one]
  have hsum : ∑ y : Ω, transition x y = (1 : ℝ≥0∞) := by
    simpa only [tsum_fintype] using (PMF.tsum_coe (transition x))
  calc
    ∑ y : Ω, (transition x y).toReal =
        (∑ y : Ω, transition x y).toReal := by
          symm
          rw [ENNReal.toReal_sum]
          intro y _hy
          exact (transition x).apply_ne_top y
    _ = 1 := by rw [hsum]; simp

/-- Real expectation under a finite PMF commutes with multiplication by a real
constant. -/
theorem finite_pmfExpectationReal_const_mul
    {α : Type*} [Fintype α]
    (p : PMF α) (c : ℝ) (f : α → ℝ) :
    finitePMFExpectationReal p (fun x => c * f x) =
      c * finitePMFExpectationReal p f := by
  classical
  unfold finitePMFExpectationReal
  calc
    ∑ x : α, (p x).toReal * (c * f x) =
        ∑ x : α, c * ((p x).toReal * f x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = c * ∑ x : α, (p x).toReal * f x := by
      rw [Finset.mul_sum]

/-- The product cylinder observable associated with a tuple of time-indexed
observables and a finite path. -/
def linearMarkovFinitePathProduct
    {Ω : Type*}
    {n : ℕ}
    (fs : Fin (n + 1) → Ω → ℝ)
    (path : Fin (n + 1) → Ω) : ℝ :=
  ∏ i : Fin (n + 1), fs i (path i)

/-- Contract the last two observables of a finite cylinder using the transition
operator. This is the terminal-coordinate form of backward Markov
conditioning. -/
def linearMarkovFiniteCylinderContractLast
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) :
    (n : ℕ) →
      (Fin (n + 2) → Ω → ℝ) →
        Fin (n + 1) → Ω → ℝ
  | 0, fs => fun _ x => fs 0 x * P (fs 1) x
  | n + 1, fs =>
      Fin.cons (fs 0)
        (linearMarkovFiniteCylinderContractLast P n (Fin.tail fs))

/-- Contracting the last two observables preserves the backward cylinder
condition. -/
theorem linearMarkovCylinderCondition_ofFn_contractLast
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ : Ω => (1 : ℝ)) = fun _ : Ω => 1)
    (n : ℕ)
    (fs : Fin (n + 2) → Ω → ℝ) :
    linearMarkovCylinderCondition P (List.ofFn fs) =
      linearMarkovCylinderCondition P
        (List.ofFn (linearMarkovFiniteCylinderContractLast P n fs)) := by
  induction n with
  | zero =>
      funext x
      simp [linearMarkovFiniteCylinderContractLast,
        linearMarkovCylinderCondition, hPone]
  | succ n ih =>
      rw [← Fin.cons_self_tail fs]
      simp only [List.ofFn_cons, linearMarkovFiniteCylinderContractLast,
        Fin.cons_zero, Fin.tail_cons]
      funext x
      simp only [linearMarkovCylinderCondition_cons]
      rw [ih (Fin.tail fs)]

/-- Pointwise, terminal contraction changes the product cylinder exactly by
multiplying the previous path product with the expected terminal observable. -/
theorem linearMarkovFinitePathProduct_contractLast
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (n : ℕ)
    (fs : Fin (n + 2) → Ω → ℝ)
    (path : Fin (n + 1) → Ω) :
    linearMarkovFinitePathProduct
        (linearMarkovFiniteCylinderContractLast P n fs) path =
      linearMarkovFinitePathProduct
          (fun i : Fin (n + 1) => fs i.castSucc) path *
        P (fs (Fin.last (n + 1))) (path (Fin.last n)) := by
  induction n with
  | zero =>
      simp [linearMarkovFinitePathProduct,
        linearMarkovFiniteCylinderContractLast]
  | succ n ih =>
      have hleft :
          linearMarkovFinitePathProduct
              (linearMarkovFiniteCylinderContractLast P (n + 1) fs) path =
            fs 0 (path 0) *
              linearMarkovFinitePathProduct
                (linearMarkovFiniteCylinderContractLast P n (Fin.tail fs))
                (Fin.tail path) := by
        unfold linearMarkovFinitePathProduct
        rw [Fin.prod_univ_succ]
        simp [linearMarkovFiniteCylinderContractLast, Fin.tail]
      have hright :
          linearMarkovFinitePathProduct
              (fun i : Fin (n + 2) => fs i.castSucc) path =
            fs 0 (path 0) *
              linearMarkovFinitePathProduct
                (fun i : Fin (n + 1) => (Fin.tail fs) i.castSucc)
                (Fin.tail path) := by
        unfold linearMarkovFinitePathProduct
        rw [Fin.prod_univ_succ]
        simp [Fin.tail]
      rw [hleft, ih (Fin.tail fs) (Fin.tail path), hright]
      simp [Fin.tail]
      ring

/-- The honest arbitrary finite Markov path PMF realizes exactly the existing
backward finite-cylinder moment recursion. -/
theorem linearMarkovFinitePathPMF_product_expectation_eq_cylinderMoment
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ) :
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (linearMarkovFinitePathProduct fs) =
      linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs) := by
  let P := finitePMFTransitionExpectationLinearMap transition
  change
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (linearMarkovFinitePathProduct fs) =
      linearMarkovCylinderMoment
        (finitePMFExpectationReal initial) P (List.ofFn fs)
  have hPone : P (fun _ : Ω => (1 : ℝ)) = fun _ : Ω => 1 :=
    finitePMFTransitionExpectationLinearMap_one transition
  induction n with
  | zero =>
      rw [linearMarkovFinitePathPMF, finite_pmfExpectationReal_map]
      unfold linearMarkovCylinderMoment
      have hfs : List.ofFn fs = [fs 0] := by
        rw [List.ofFn_succ']
        simp
      rw [hfs, linearMarkovCylinderCondition_singleton P hPone]
      congr 1
      funext x
      simp [linearMarkovFinitePathProduct]
  | succ n ih =>
      rw [linearMarkovFinitePathPMF, finite_pmfExpectationReal_bind]
      simp_rw [finite_pmfExpectationReal_map]
      calc
        finitePMFExpectationReal
            (linearMarkovFinitePathPMF initial transition n)
            (fun path =>
              finitePMFExpectationReal
                (transition (path (Fin.last n)))
                (fun y =>
                  linearMarkovFinitePathProduct fs (Fin.snoc path y))) =
          finitePMFExpectationReal
            (linearMarkovFinitePathPMF initial transition n)
            (linearMarkovFinitePathProduct
              (linearMarkovFiniteCylinderContractLast P n fs)) := by
                apply congrArg
                  (finitePMFExpectationReal
                    (linearMarkovFinitePathPMF initial transition n))
                funext path
                calc
                  finitePMFExpectationReal
                      (transition (path (Fin.last n)))
                      (fun y =>
                        linearMarkovFinitePathProduct fs
                          (Fin.snoc path y)) =
                    finitePMFExpectationReal
                      (transition (path (Fin.last n)))
                      (fun y =>
                        linearMarkovFinitePathProduct
                            (fun i : Fin (n + 1) => fs i.castSucc) path *
                          fs (Fin.last (n + 1)) y) := by
                            congr 1
                            funext y
                            simp [linearMarkovFinitePathProduct,
                              Fin.prod_univ_castSucc]
                  _ =
                    linearMarkovFinitePathProduct
                        (fun i : Fin (n + 1) => fs i.castSucc) path *
                      P (fs (Fin.last (n + 1)))
                        (path (Fin.last n)) := by
                          rw [finite_pmfExpectationReal_const_mul]
                          rfl
                  _ =
                    linearMarkovFinitePathProduct
                      (linearMarkovFiniteCylinderContractLast P n fs) path := by
                        symm
                        exact
                          linearMarkovFinitePathProduct_contractLast
                            P n fs path
        _ =
          linearMarkovCylinderMoment
            (finitePMFExpectationReal initial) P
            (List.ofFn
              (linearMarkovFiniteCylinderContractLast P n fs)) :=
                ih (linearMarkovFiniteCylinderContractLast P n fs)
        _ =
          linearMarkovCylinderMoment
            (finitePMFExpectationReal initial) P (List.ofFn fs) := by
              unfold linearMarkovCylinderMoment
              rw [← linearMarkovCylinderCondition_ofFn_contractLast
                P hPone n fs]

end

end MathlibAnalytic
end MGAP4D
