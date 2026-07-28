import MGAP4D.MathlibAnalytic.LinearMarkovIntegerPathShift
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Keep the first `n + 1` coordinates of a path with `n + d` transitions. -/
def linearMarkovFinitePathInitBy
    {Ω : Type*} (n d : ℕ)
    (path : Fin (n + d + 1) → Ω) : Fin (n + 1) → Ω :=
  fun i => path ⟨i.1, by omega⟩

/-- Keep the last `n + 1` coordinates of a path with `n + d` transitions. -/
def linearMarkovFinitePathTailBy
    {Ω : Type*} (n d : ℕ)
    (path : Fin (n + d + 1) → Ω) : Fin (n + 1) → Ω :=
  fun i => path ⟨i.1 + d, by omega⟩

@[simp] theorem linearMarkovFinitePathInitBy_apply
    {Ω : Type*} (n d : ℕ)
    (path : Fin (n + d + 1) → Ω) (i : Fin (n + 1)) :
    linearMarkovFinitePathInitBy n d path i = path ⟨i.1, by omega⟩ :=
  rfl

@[simp] theorem linearMarkovFinitePathTailBy_apply
    {Ω : Type*} (n d : ℕ)
    (path : Fin (n + d + 1) → Ω) (i : Fin (n + 1)) :
    linearMarkovFinitePathTailBy n d path i = path ⟨i.1 + d, by omega⟩ :=
  rfl

@[simp] theorem linearMarkovFinitePathInitBy_zero
    {Ω : Type*} (n : ℕ) (path : Fin (n + 1) → Ω) :
    linearMarkovFinitePathInitBy n 0 path = path := by
  funext i
  rfl

@[simp] theorem linearMarkovFinitePathTailBy_zero
    {Ω : Type*} (n : ℕ) (path : Fin (n + 1) → Ω) :
    linearMarkovFinitePathTailBy n 0 path = path := by
  funext i
  rfl

/-- Iterated terminal deletion is one `Fin.init` followed by the shorter
restriction. -/
theorem linearMarkovFinitePathInitBy_succ
    {Ω : Type*} (n d : ℕ)
    (path : Fin (n + (d + 1) + 1) → Ω) :
    linearMarkovFinitePathInitBy n (d + 1) path =
      linearMarkovFinitePathInitBy n d (Fin.init path) := by
  funext i
  rfl

/-- Iterated initial deletion is one `Fin.tail` followed by the shorter
restriction. -/
theorem linearMarkovFinitePathTailBy_succ
    {Ω : Type*} (n d : ℕ)
    (path : Fin (n + (d + 1) + 1) → Ω) :
    linearMarkovFinitePathTailBy n (d + 1) path =
      linearMarkovFinitePathTailBy n d (Fin.tail path) := by
  funext i
  apply congrArg path
  apply Fin.ext
  simp
  omega

/-- Deleting any finite number of terminal coordinates recovers the shorter
finite Markov path law. -/
theorem linearMarkovFinitePathPMF_map_initBy
    {Ω : Type*}
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (n d : ℕ) :
    (linearMarkovFinitePathPMF initial transition (n + d)).map
        (linearMarkovFinitePathInitBy n d) =
      linearMarkovFinitePathPMF initial transition n := by
  induction d with
  | zero =>
      simpa using PMF.map_id
        (linearMarkovFinitePathPMF initial transition n)
  | succ d ih =>
      rw [show linearMarkovFinitePathInitBy n (d + 1) =
          linearMarkovFinitePathInitBy n d ∘ Fin.init by
        funext path
        exact linearMarkovFinitePathInitBy_succ n d path]
      rw [← PMF.map_comp]
      have hstep :
          (linearMarkovFinitePathPMF initial transition (n + (d + 1))).map Fin.init =
            linearMarkovFinitePathPMF initial transition (n + d) := by
        simpa only [Nat.add_succ] using
          linearMarkovFinitePathPMF_succ_map_init
            initial transition (n + d)
      rw [hstep]
      exact ih

/-- Under detailed balance, deleting any finite number of initial coordinates
also recovers the shorter finite Markov path law. -/
theorem linearMarkovFinitePathPMF_map_tailBy_of_detailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n d : ℕ) :
    (linearMarkovFinitePathPMF initial transition (n + d)).map
        (linearMarkovFinitePathTailBy n d) =
      linearMarkovFinitePathPMF initial transition n := by
  induction d with
  | zero =>
      simpa using PMF.map_id
        (linearMarkovFinitePathPMF initial transition n)
  | succ d ih =>
      rw [show linearMarkovFinitePathTailBy n (d + 1) =
          linearMarkovFinitePathTailBy n d ∘ Fin.tail by
        funext path
        exact linearMarkovFinitePathTailBy_succ n d path]
      rw [← PMF.map_comp]
      have hstep :
          (linearMarkovFinitePathPMF initial transition (n + (d + 1))).map
              (Fin.tail :
                (Fin (n + (d + 1) + 1) → Ω) →
                  (Fin (n + d + 1) → Ω)) =
            linearMarkovFinitePathPMF initial transition (n + d) := by
        simpa only [Nat.add_succ] using
          linearMarkovFinitePathPMF_succ_map_tail_of_detailedBalanceReal
            initial transition hdb (n + d)
      rw [hstep]
      exact ih

end

end MathlibAnalytic
end MGAP4D
