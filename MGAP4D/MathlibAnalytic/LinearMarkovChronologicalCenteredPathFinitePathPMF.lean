import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concatenate an `m`-transition prefix with an `n + 1`-coordinate strictly
positive future.  The output has `m + n + 1` transitions. -/
def linearMarkovAppendFinitePath
    {Ω : Type*} {m n : ℕ}
    (past : Fin (m + 1) → Ω)
    (future : Fin (n + 1) → Ω) :
    Fin ((m + n + 1) + 1) → Ω :=
  Fin.append past future ∘ Fin.cast (by omega)

/-- Appending a one-coordinate future is the ordinary terminal `snoc`. -/
@[simp] theorem linearMarkovAppendFinitePath_zero
    {Ω : Type*} {m : ℕ}
    (past : Fin (m + 1) → Ω) (y : Ω) :
    linearMarkovAppendFinitePath past (fun _ : Fin 1 => y) =
      (Fin.snoc past y : Fin (m + 2) → Ω) := by
  funext i
  simp [linearMarkovAppendFinitePath, Function.comp_def]

/-- Extending the future and then concatenating equals extending the already
concatenated path. -/
@[simp] theorem linearMarkovAppendFinitePath_snoc
    {Ω : Type*} {m n : ℕ}
    (past : Fin (m + 1) → Ω)
    (future : Fin (n + 1) → Ω)
    (y : Ω) :
    linearMarkovAppendFinitePath past (Fin.snoc future y) =
      (Fin.snoc (linearMarkovAppendFinitePath past future) y :
        Fin ((m + (n + 1) + 1) + 1) → Ω) := by
  funext i
  simp [linearMarkovAppendFinitePath, Function.comp_def, Fin.append_snoc]

/-- The terminal state of a concatenated path is the terminal state of its
strictly-positive future. -/
@[simp] theorem linearMarkovAppendFinitePath_last
    {Ω : Type*} {m n : ℕ}
    (past : Fin (m + 1) → Ω)
    (future : Fin (n + 1) → Ω) :
    linearMarkovAppendFinitePath past future (Fin.last (m + n + 1)) =
      future (Fin.last n) := by
  simp [linearMarkovAppendFinitePath, Function.comp_def]

/-- The law obtained by sampling a finite prefix and then an independent
conditional continuation from its terminal state. -/
def linearMarkovFinitePathSplitPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (m n : ℕ) :
    PMF (Fin ((m + n + 1) + 1) → Ω) :=
  (linearMarkovFinitePathPMF initial transition m).bind fun past =>
    (linearMarkovPositiveTimeFuturePMF transition n
      (past (Fin.last m))).map
        (linearMarkovAppendFinitePath past)

/-- Adding one transition to the conditional future extends the concatenated
split law by the ordinary Markov terminal kernel. -/
theorem linearMarkovFinitePathSplitPMF_succ
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (m n : ℕ) :
    linearMarkovFinitePathSplitPMF initial transition m (n + 1) =
      (linearMarkovFinitePathSplitPMF initial transition m n).bind fun path =>
        (transition (path (Fin.last (m + n + 1)))).map fun y =>
          (Fin.snoc path y : Fin ((m + (n + 1) + 1) + 1) → Ω) := by
  unfold linearMarkovFinitePathSplitPMF
    linearMarkovPositiveTimeFuturePMF
  rw [linearMarkovFinitePathPMF]
  rw [PMF.map_bind]
  rw [PMF.bind_bind]
  apply congrArg (PMF.bind (linearMarkovFinitePathPMF initial transition m))
  funext past
  rw [PMF.bind_map]
  rw [PMF.bind_bind]
  apply congrArg
    (PMF.bind
      (linearMarkovFinitePathPMF
        (transition (past (Fin.last m))) transition n))
  funext future
  rw [PMF.map_comp]
  simp only [Function.comp_apply]
  congr 1
  funext y
  simp

/-- Exact Markov concatenation: sampling a prefix and then its conditional
future gives the same PMF as sampling the entire finite path at once. -/
theorem linearMarkovFinitePathSplitPMF_eq_finitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (m n : ℕ) :
    linearMarkovFinitePathSplitPMF initial transition m n =
      linearMarkovFinitePathPMF initial transition (m + n + 1) := by
  induction n with
  | zero =>
      unfold linearMarkovFinitePathSplitPMF
        linearMarkovPositiveTimeFuturePMF
      rw [linearMarkovFinitePathPMF]
      rw [linearMarkovFinitePathPMF]
      apply congrArg (PMF.bind (linearMarkovFinitePathPMF initial transition m))
      funext past
      rw [PMF.map_comp]
      simp only [Function.comp_apply]
      congr 1
      funext y
      simp
  | succ n ih =>
      rw [linearMarkovFinitePathSplitPMF_succ]
      rw [ih]
      rw [show m + (n + 1) + 1 = (m + n + 1) + 1 by omega]
      rw [linearMarkovFinitePathPMF]

/-- Packing a single-chain centered decomposition simply concatenates its
chronological past segment with its positive continuation. -/
@[simp] theorem linearMarkovCenteredFinitePathToChronological_singleChain
    {Ω : Type*} {n : ℕ}
    (past : Fin (n + 2) → Ω)
    (positive : LinearMarkovPositiveTimeFuturePath Ω n) :
    linearMarkovCenteredFinitePathToChronological
        (linearMarkovSingleChainCenteredFinitePath past positive) =
      linearMarkovAppendFinitePath past positive := by
  apply funext
  intro i
  simp [linearMarkovCenteredFinitePathToChronological,
    linearMarkovChronologicalSumToExplicit,
    linearMarkovCenteredFinitePathToChronologicalSum,
    linearMarkovSingleChainCenteredFinitePath,
    linearMarkovAppendFinitePath, Function.comp_def]

/-- The explicit chronological centered law is exactly one ordinary finite
Markov path law.  Detailed balance is not needed for this identity. -/
theorem linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    linearMarkovChronologicalCenteredFinitePathPMF initial transition n =
      linearMarkovFinitePathPMF initial transition (2 * n + 2) := by
  unfold linearMarkovChronologicalCenteredFinitePathPMF
    linearMarkovSingleChainCenteredFinitePathPMF
  rw [PMF.map_bind]
  apply Eq.trans _
    (linearMarkovFinitePathSplitPMF_eq_finitePathPMF
      initial transition (n + 1) n)
  apply congrArg
    (PMF.bind (linearMarkovFinitePathPMF initial transition (n + 1)))
  funext past
  rw [PMF.map_comp]
  simp only [Function.comp_apply]
  congr 1
  funext positive
  exact linearMarkovCenteredFinitePathToChronological_singleChain past positive

end

end MathlibAnalytic
end MGAP4D
