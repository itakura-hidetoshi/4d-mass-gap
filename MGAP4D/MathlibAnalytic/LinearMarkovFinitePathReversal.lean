import MGAP4D.MathlibAnalytic.LinearMarkovDetailedBalancePairLaw
import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPMF
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Reverse every coordinate of an `n`-transition finite path. -/
def linearMarkovFinitePathReverse
    {Ω : Type*} {n : ℕ}
    (path : Fin (n + 1) → Ω) : Fin (n + 1) → Ω :=
  fun i => path i.rev

@[simp] theorem linearMarkovFinitePathReverse_apply
    {Ω : Type*} {n : ℕ}
    (path : Fin (n + 1) → Ω) (i : Fin (n + 1)) :
    linearMarkovFinitePathReverse path i = path i.rev :=
  rfl

/-- Finite path reversal is involutive. -/
@[simp] theorem linearMarkovFinitePathReverse_involutive
    {Ω : Type*} (n : ℕ) :
    Function.Involutive
      (@linearMarkovFinitePathReverse Ω n) := by
  intro path
  funext i
  simp [linearMarkovFinitePathReverse]

/-- Finite path reversal as an equivalence of the finite path carrier. -/
def linearMarkovFinitePathReverseEquiv
    {Ω : Type*} (n : ℕ) :
    (Fin (n + 1) → Ω) ≃ (Fin (n + 1) → Ω) :=
  (linearMarkovFinitePathReverse_involutive (Ω := Ω) n).toPerm

/-- The recursively appended finite path PMF has the expected point-mass
factorization into its preceding path mass and terminal transition mass. -/
theorem linearMarkovFinitePathPMF_apply_succ
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (path : Fin (n + 2) → Ω) :
    linearMarkovFinitePathPMF initial transition (n + 1) path =
      linearMarkovFinitePathPMF initial transition n (Fin.init path) *
        transition ((Fin.init path) (Fin.last n))
          (path (Fin.last (n + 1))) := by
  classical
  let inner (old : Fin (n + 1) → Ω) : ℝ≥0∞ :=
    ∑ y : Ω,
      @ite ℝ≥0∞ (path = Fin.snoc old y)
        (Classical.propDecidable (path = Fin.snoc old y))
        (transition (old (Fin.last n)) y) 0
  have hinner (old : Fin (n + 1) → Ω) :
      inner old =
        if old = Fin.init path then
          transition ((Fin.init path) (Fin.last n))
            (path (Fin.last (n + 1)))
        else 0 := by
    unfold inner
    by_cases hold : old = Fin.init path
    · subst old
      have heq : ∀ y : Ω,
          path = Fin.snoc (Fin.init path) y ↔
            y = path (Fin.last (n + 1)) := by
        intro y
        constructor
        · intro h
          have hlast := congrArg (fun q => q (Fin.last (n + 1))) h
          simpa using hlast.symm
        · intro h
          subst y
          exact (Fin.snoc_init_self path).symm
      simp_rw [heq]
      calc
        (∑ y : Ω,
          if y = path (Fin.last (n + 1)) then
            transition ((Fin.init path) (Fin.last n)) y
          else 0) =
          (if path (Fin.last (n + 1)) = path (Fin.last (n + 1)) then
            transition ((Fin.init path) (Fin.last n))
              (path (Fin.last (n + 1)))
          else 0) := by
            apply Finset.sum_eq_single (path (Fin.last (n + 1)))
            · intro y _hy hne
              simp [hne]
            · simp
        _ = transition ((Fin.init path) (Fin.last n))
              (path (Fin.last (n + 1))) := by
              simp
    · have hsnoc : ∀ y : Ω, path ≠ Fin.snoc old y := by
        intro y hy
        apply hold
        have hinit := congrArg Fin.init hy
        rw [Fin.init_snoc] at hinit
        exact hinit.symm
      have hleft :
          (∑ y : Ω,
            if path = Fin.snoc old y then
              transition (old (Fin.last n)) y
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro y _hy
        rw [if_neg (hsnoc y)]
      rw [hleft, if_neg hold]
  rw [linearMarkovFinitePathPMF, PMF.bind_apply, tsum_fintype]
  simp_rw [PMF.map_apply, tsum_fintype]
  change
    (∑ old : Fin (n + 1) → Ω,
      linearMarkovFinitePathPMF initial transition n old * inner old) =
      linearMarkovFinitePathPMF initial transition n (Fin.init path) *
        transition ((Fin.init path) (Fin.last n))
          (path (Fin.last (n + 1)))
  calc
    (∑ old : Fin (n + 1) → Ω,
      linearMarkovFinitePathPMF initial transition n old * inner old) =
      (∑ old : Fin (n + 1) → Ω,
        linearMarkovFinitePathPMF initial transition n old *
          (if old = Fin.init path then
            transition ((Fin.init path) (Fin.last n))
              (path (Fin.last (n + 1)))
          else 0)) := by
            apply Finset.sum_congr rfl
            intro old _hold
            rw [hinner old]
    _ = linearMarkovFinitePathPMF initial transition n (Fin.init path) *
        (if Fin.init path = Fin.init path then
          transition ((Fin.init path) (Fin.last n))
            (path (Fin.last (n + 1)))
        else 0) := by
          apply Finset.sum_eq_single (Fin.init path)
          · intro old _hold hne
            simp [hne]
          · simp
    _ = linearMarkovFinitePathPMF initial transition n (Fin.init path) *
        transition ((Fin.init path) (Fin.last n))
          (path (Fin.last (n + 1))) := by
          simp

/-- The zero-transition finite path PMF evaluates to the initial point mass. -/
theorem linearMarkovFinitePathPMF_apply_zero
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (path : Fin 1 → Ω) :
    linearMarkovFinitePathPMF initial transition 0 path =
      initial (path 0) := by
  classical
  rw [linearMarkovFinitePathPMF, PMF.map_apply, tsum_fintype]
  have hconst : ∀ x : Ω,
      path = (fun _ : Fin 1 => x) ↔ x = path 0 := by
    intro x
    constructor
    · intro h
      simpa [h]
    · intro h
      funext i
      fin_cases i
      simpa using h.symm
  simp_rw [hconst]
  simp

/-- Real point probability of a finite Markov path, written as initial real mass
multiplied by the product of all consecutive transition real masses. -/
def linearMarkovFinitePathProbabilityReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    {n : ℕ}
    (path : Fin (n + 1) → Ω) : ℝ :=
  (initial (path 0)).toReal *
    ∏ i : Fin n,
      (transition (path i.castSucc) (path i.succ)).toReal

/-- The honest finite path PMF point mass is exactly the explicit consecutive
transition product. -/
theorem linearMarkovFinitePathPMF_toReal_eq_probabilityReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (path : Fin (n + 1) → Ω) :
    (linearMarkovFinitePathPMF initial transition n path).toReal =
      linearMarkovFinitePathProbabilityReal initial transition path := by
  induction n with
  | zero =>
      rw [linearMarkovFinitePathPMF_apply_zero]
      simp [linearMarkovFinitePathProbabilityReal]
  | succ n ih =>
      rw [linearMarkovFinitePathPMF_apply_succ, ENNReal.toReal_mul,
        ih (Fin.init path)]
      unfold linearMarkovFinitePathProbabilityReal
      rw [Fin.prod_univ_castSucc]
      simp [Fin.init, mul_assoc]

/-- Detailed balance transports the initial endpoint mass through every edge of
one finite path, reversing all transition factors. -/
theorem linearMarkovFinitePath_endpoint_weight_reversal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (path : Fin (n + 1) → Ω) :
    (initial (path 0)).toReal *
        ∏ i : Fin n,
          (transition (path i.castSucc) (path i.succ)).toReal =
      (initial (path (Fin.last n))).toReal *
        ∏ i : Fin n,
          (transition (path i.succ) (path i.castSucc)).toReal := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let tailPath : Fin (n + 1) → Ω := Fin.tail path
      let forwardTail : ℝ :=
        ∏ i : Fin n,
          (transition (tailPath i.castSucc) (tailPath i.succ)).toReal
      let backwardTail : ℝ :=
        ∏ i : Fin n,
          (transition (tailPath i.succ) (tailPath i.castSucc)).toReal
      have hforward :
          (∏ i : Fin (n + 1),
            (transition (path i.castSucc) (path i.succ)).toReal) =
            (transition (path 0) (path 1)).toReal * forwardTail := by
        rw [Fin.prod_univ_succ]
        simp [forwardTail, tailPath, Fin.tail]
      have hbackward :
          (∏ i : Fin (n + 1),
            (transition (path i.succ) (path i.castSucc)).toReal) =
            (transition (path 1) (path 0)).toReal * backwardTail := by
        rw [Fin.prod_univ_succ]
        simp [backwardTail, tailPath, Fin.tail]
      have ihtail :
          (initial (path 1)).toReal * forwardTail =
            (initial (path (Fin.last (n + 1)))).toReal * backwardTail := by
        simpa [forwardTail, backwardTail, tailPath, Fin.tail] using
          ih (Fin.tail path)
      rw [hforward, hbackward]
      calc
        (initial (path 0)).toReal *
            ((transition (path 0) (path 1)).toReal * forwardTail) =
          ((initial (path 0)).toReal *
            (transition (path 0) (path 1)).toReal) * forwardTail := by
              ring
        _ = ((initial (path 1)).toReal *
            (transition (path 1) (path 0)).toReal) * forwardTail := by
              rw [hdb (path 0) (path 1)]
        _ = (transition (path 1) (path 0)).toReal *
            ((initial (path 1)).toReal * forwardTail) := by
              ring
        _ = (transition (path 1) (path 0)).toReal *
            ((initial (path (Fin.last (n + 1)))).toReal * backwardTail) := by
              rw [ihtail]
        _ = (initial (path (Fin.last (n + 1)))).toReal *
            ((transition (path 1) (path 0)).toReal * backwardTail) := by
              ring

/-- The explicit real path probability of the reversed path is the endpoint
mass multiplied by all transition factors in the backward direction. -/
theorem linearMarkovFinitePathProbabilityReal_reverse_eq_backward
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (path : Fin (n + 1) → Ω) :
    linearMarkovFinitePathProbabilityReal initial transition
        (linearMarkovFinitePathReverse path) =
      (initial (path (Fin.last n))).toReal *
        ∏ i : Fin n,
          (transition (path i.succ) (path i.castSucc)).toReal := by
  unfold linearMarkovFinitePathProbabilityReal
  have hfirst :
      linearMarkovFinitePathReverse path 0 = path (Fin.last n) := by
    simp [linearMarkovFinitePathReverse]
  rw [hfirst]
  apply congrArg
    (fun r : ℝ => (initial (path (Fin.last n))).toReal * r)
  rw [← Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n))]
  apply Finset.prod_congr rfl
  intro i _hi
  simp only [Fin.revPerm_apply, linearMarkovFinitePathReverse_apply]
  simp only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]

/-- Detailed balance makes every explicit finite path probability invariant under
complete path reversal. -/
theorem linearMarkovFinitePathProbabilityReal_reverse_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (path : Fin (n + 1) → Ω) :
    linearMarkovFinitePathProbabilityReal initial transition
        (linearMarkovFinitePathReverse path) =
      linearMarkovFinitePathProbabilityReal initial transition path := by
  rw [linearMarkovFinitePathProbabilityReal_reverse_eq_backward]
  exact
    (linearMarkovFinitePath_endpoint_weight_reversal
      initial transition hdb n path).symm

/-- Every point mass of a detailed-balanced finite path law is unchanged by
complete path reversal. -/
theorem linearMarkovFinitePathPMF_toReal_reverse_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (path : Fin (n + 1) → Ω) :
    (linearMarkovFinitePathPMF initial transition n
        (linearMarkovFinitePathReverse path)).toReal =
      (linearMarkovFinitePathPMF initial transition n path).toReal := by
  rw [linearMarkovFinitePathPMF_toReal_eq_probabilityReal,
    linearMarkovFinitePathPMF_toReal_eq_probabilityReal]
  exact
    linearMarkovFinitePathProbabilityReal_reverse_of_detailedBalance
      initial transition hdb n path

/-- Expectation under every finite detailed-balanced path law is invariant under
complete path reversal. -/
theorem linearMarkovFinitePathPMF_expectation_reverse_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (H : (Fin (n + 1) → Ω) → ℝ) :
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (H ∘ linearMarkovFinitePathReverse) =
      finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n) H := by
  classical
  unfold finitePMFExpectationReal
  let e := linearMarkovFinitePathReverseEquiv (Ω := Ω) n
  calc
    ∑ path : Fin (n + 1) → Ω,
        (linearMarkovFinitePathPMF initial transition n path).toReal *
          (H ∘ linearMarkovFinitePathReverse) path =
      ∑ path : Fin (n + 1) → Ω,
        (linearMarkovFinitePathPMF initial transition n
          (linearMarkovFinitePathReverse path)).toReal * H path := by
            rw [← Equiv.sum_comp e]
            apply Finset.sum_congr rfl
            intro path _hpath
            change
              (linearMarkovFinitePathPMF initial transition n
                  (linearMarkovFinitePathReverse path)).toReal *
                    H (linearMarkovFinitePathReverse
                      (linearMarkovFinitePathReverse path)) =
                (linearMarkovFinitePathPMF initial transition n
                  (linearMarkovFinitePathReverse path)).toReal * H path
            rw [linearMarkovFinitePathReverse_involutive (Ω := Ω) n path]
    _ = ∑ path : Fin (n + 1) → Ω,
        (linearMarkovFinitePathPMF initial transition n path).toReal * H path := by
          apply Finset.sum_congr rfl
          intro path _hpath
          rw [linearMarkovFinitePathPMF_toReal_reverse_of_detailedBalance
            initial transition hdb n path]

/-- Every arbitrary-length finite Markov path PMF satisfying detailed balance is
exactly invariant under complete time reversal. -/
theorem linearMarkovFinitePathPMF_map_reverse_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition n).map
        linearMarkovFinitePathReverse =
      linearMarkovFinitePathPMF initial transition n := by
  apply finite_pmf_eq_of_expectationReal_eq
  intro H
  rw [finite_pmfExpectationReal_map]
  simpa [Function.comp_def] using
    linearMarkovFinitePathPMF_expectation_reverse_of_detailedBalance
      initial transition hdb n H

end

end MathlibAnalytic
end MGAP4D
