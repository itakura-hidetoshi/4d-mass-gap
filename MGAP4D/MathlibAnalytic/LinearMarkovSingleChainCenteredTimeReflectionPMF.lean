import MGAP4D.MathlibAnalytic.LinearMarkovCenteredTimeReflectionPMF
import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathReversal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The negative-time half extracted from one chronological past segment.  The
past includes its terminal time-zero boundary, so complete reversal followed by
deletion of the first reversed coordinate gives the reflected coordinates
`X₋₁, ..., X₋ₙ₋₁`. -/
def linearMarkovSingleChainReflectedPast
    {Ω : Type*} {n : ℕ}
    (past : Fin (n + 2) → Ω) :
    LinearMarkovPositiveTimeFuturePath Ω n :=
  Fin.tail (linearMarkovFinitePathReverse past)

/-- Reversing an already reversed chronological segment recovers its ordinary
tail. -/
@[simp] theorem linearMarkovSingleChainReflectedPast_reverse
    {Ω : Type*} {n : ℕ}
    (path : Fin (n + 2) → Ω) :
    linearMarkovSingleChainReflectedPast
        (linearMarkovFinitePathReverse path) =
      Fin.tail path := by
  unfold linearMarkovSingleChainReflectedPast
  exact congrArg Fin.tail
    (linearMarkovFinitePathReverse_involutive (Ω := Ω) (n + 1) path)

/-- The terminal coordinate of a reversed finite segment is its original first
coordinate. -/
@[simp] theorem linearMarkovFinitePathReverse_last
    {Ω : Type*} {n : ℕ}
    (path : Fin (n + 2) → Ω) :
    linearMarkovFinitePathReverse path (Fin.last (n + 1)) = path 0 := by
  simp [linearMarkovFinitePathReverse]

/-- Split one chronological finite Markov chain at its terminal time-zero
boundary.  Its past is reflected away from the boundary and its future is the
ordinary continuation from that same boundary. -/
def linearMarkovSingleChainCenteredFinitePath
    {Ω : Type*} {n : ℕ}
    (past : Fin (n + 2) → Ω)
    (positive : LinearMarkovPositiveTimeFuturePath Ω n) :
    LinearMarkovCenteredFinitePath Ω n :=
  ⟨linearMarkovSingleChainReflectedPast past,
    past (Fin.last (n + 1)), positive⟩

/-- After reversing a path written as boundary followed by a future, the
single-chain centered decomposition has exactly that future as its reflected
past. -/
@[simp] theorem linearMarkovSingleChainCenteredFinitePath_reverse_cons
    {Ω : Type*} {n : ℕ}
    (boundary : Ω)
    (negative positive : LinearMarkovPositiveTimeFuturePath Ω n) :
    linearMarkovSingleChainCenteredFinitePath
        (linearMarkovFinitePathReverse (Fin.cons boundary negative)) positive =
      (⟨negative, boundary, positive⟩ :
        LinearMarkovCenteredFinitePath Ω n) := by
  simp [linearMarkovSingleChainCenteredFinitePath]

/-- Every finite Markov path is obtained by first sampling its time-zero state
and then sampling the strictly-positive-time conditional future. -/
theorem linearMarkovFinitePathPMF_eq_initial_bind_positiveTimeFuture
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    linearMarkovFinitePathPMF initial transition (n + 1) =
      initial.bind fun boundary =>
        (linearMarkovPositiveTimeFuturePMF transition n boundary).map
          (fun future => Fin.cons boundary future) := by
  induction n with
  | zero =>
      change
        ((initial.map fun x => (fun _ : Fin 1 => x)).bind fun path =>
            (transition (path (Fin.last 0))).map fun y =>
              (Fin.snoc path y : Fin 2 → Ω)) =
          initial.bind fun boundary =>
            ((transition boundary).map fun x => (fun _ : Fin 1 => x)).map
              (fun future : Fin 1 → Ω =>
                (Fin.cons boundary future : Fin 2 → Ω))
      rw [PMF.bind_map]
      apply congrArg (PMF.bind initial)
      funext boundary
      rw [PMF.map_comp]
      simp only [Function.comp_apply]
      congr 1
      funext y
      funext i
      fin_cases i <;> rfl
  | succ n ih =>
      rw [linearMarkovFinitePathPMF]
      rw [ih]
      rw [PMF.bind_bind]
      apply congrArg (PMF.bind initial)
      funext boundary
      rw [PMF.bind_map]
      unfold linearMarkovPositiveTimeFuturePMF
      rw [linearMarkovFinitePathPMF, PMF.map_bind]
      apply congrArg
        (PMF.bind (linearMarkovFinitePathPMF (transition boundary) transition n))
      funext future
      have hlast :
          (Fin.cons boundary future : Fin (n + 2) → Ω) (Fin.last (n + 1)) =
            future (Fin.last n) := by
        simp
      rw [hlast]
      change
        (transition (future (Fin.last n))).map
            (fun y =>
              (Fin.snoc (Fin.cons boundary future) y : Fin (n + 3) → Ω)) =
          ((transition (future (Fin.last n))).map
              (fun y => (Fin.snoc future y : Fin (n + 2) → Ω))).map
            (fun path : Fin (n + 2) → Ω =>
              (Fin.cons boundary path : Fin (n + 3) → Ω))
      rw [PMF.map_comp]
      congr 1
      funext y
      exact (Fin.cons_snoc_eq_snoc_cons boundary future y).symm

/-- Expectation form of the exact decomposition into time zero and the
conditional positive-time future. -/
theorem linearMarkovFinitePathPMF_expectation_zero_tail
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (H : (Fin (n + 2) → Ω) → ℝ) :
    finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition (n + 1)) H =
      finitePMFExpectationReal initial
        (fun boundary =>
          finitePMFExpectationReal
            (linearMarkovPositiveTimeFuturePMF transition n boundary)
            (fun future => H (Fin.cons boundary future))) := by
  rw [linearMarkovFinitePathPMF_eq_initial_bind_positiveTimeFuture]
  rw [finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_map]

/-- The centered law obtained from one chronological finite Markov chain: first
sample a stationary past segment ending at time zero, then continue the same
transition from that terminal boundary into the positive-time future. -/
def linearMarkovSingleChainCenteredFinitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    PMF (LinearMarkovCenteredFinitePath Ω n) :=
  (linearMarkovFinitePathPMF initial transition (n + 1)).bind fun past =>
    (linearMarkovPositiveTimeFuturePMF transition n
      (past (Fin.last (n + 1)))).map
        (linearMarkovSingleChainCenteredFinitePath past)

/-- Detailed balance identifies the conditionally independent doubled-future
centered law with the past/boundary/future decomposition of one reversible
finite Markov chain. -/
theorem linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    linearMarkovSingleChainCenteredFinitePathPMF initial transition n =
      linearMarkovCenteredFinitePathPMF initial transition n := by
  apply finite_pmf_eq_of_expectationReal_eq
  intro H
  let K : (Fin (n + 2) → Ω) → ℝ := fun past =>
    finitePMFExpectationReal
      (linearMarkovPositiveTimeFuturePMF transition n
        (past (Fin.last (n + 1))))
      (fun positive =>
        H (linearMarkovSingleChainCenteredFinitePath past positive))
  calc
    finitePMFExpectationReal
        (linearMarkovSingleChainCenteredFinitePathPMF initial transition n) H =
      finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition (n + 1)) K := by
          unfold linearMarkovSingleChainCenteredFinitePathPMF
          rw [finite_pmfExpectationReal_bind]
          simp_rw [finite_pmfExpectationReal_map]
          rfl
    _ = finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition (n + 1))
        (K ∘ linearMarkovFinitePathReverse) := by
          symm
          exact linearMarkovFinitePathPMF_expectation_reverse_of_detailedBalance
            initial transition hdb (n + 1) K
    _ = finitePMFExpectationReal initial
        (fun boundary =>
          finitePMFExpectationReal
            (linearMarkovPositiveTimeFuturePMF transition n boundary)
            (fun negative =>
              finitePMFExpectationReal
                (linearMarkovPositiveTimeFuturePMF transition n boundary)
                (fun positive =>
                  H (⟨negative, boundary, positive⟩ :
                    LinearMarkovCenteredFinitePath Ω n)))) := by
          rw [linearMarkovFinitePathPMF_expectation_zero_tail]
          apply congrArg (finitePMFExpectationReal initial)
          funext boundary
          apply congrArg
            (finitePMFExpectationReal
              (linearMarkovPositiveTimeFuturePMF transition n boundary))
          funext negative
          simp [K]
    _ = finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n) H := by
          unfold linearMarkovCenteredFinitePathPMF
            linearMarkovCenteredFinitePathConditionalPMF
          rw [finite_pmfExpectationReal_bind]
          apply congrArg (finitePMFExpectationReal initial)
          funext boundary
          rw [finite_pmfExpectationReal_bind]
          simp_rw [finite_pmfExpectationReal_map]

/-- The single-chain centered law is invariant under the same finite time
reflection because it is exactly the doubled-future centered law. -/
theorem linearMarkovSingleChainCenteredFinitePathPMF_map_reflection
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovSingleChainCenteredFinitePathPMF initial transition n).map
        linearMarkovCenteredFinitePathReflection =
      linearMarkovSingleChainCenteredFinitePathPMF initial transition n := by
  rw [linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
      initial transition hdb n,
    linearMarkovCenteredFinitePathPMF_map_reflection]

/-- The temporal OS bilinear form is therefore a reflected-product expectation
under the past/boundary/future law of one reversible finite chain. -/
theorem linearMarkovSingleChainCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    finitePMFExpectationReal
        (linearMarkovSingleChainCenteredFinitePathPMF initial transition n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (linearMarkovCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift G path) =
      linearMarkovPositiveTimeOSForm initial transition n F G := by
  rw [linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
    initial transition hdb n]
  exact linearMarkovCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    initial transition n F G

end

end MathlibAnalytic
end MGAP4D
