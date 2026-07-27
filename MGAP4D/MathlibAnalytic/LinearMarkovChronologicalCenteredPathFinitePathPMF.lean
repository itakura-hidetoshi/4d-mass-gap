import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concatenate an `m`-transition prefix with an `n + 1`-coordinate strictly
positive future.  The output has `(m + 1) + n` transitions. -/
def linearMarkovAppendFinitePath
    {Ω : Type*} {m n : ℕ}
    (past : Fin (m + 1) → Ω)
    (future : Fin (n + 1) → Ω) :
    Fin (((m + 1) + n) + 1) → Ω :=
  Fin.append past future

/-- Appending a one-coordinate future is the ordinary terminal `snoc`. -/
@[simp] theorem linearMarkovAppendFinitePath_zero
    {Ω : Type*} {m : ℕ}
    (past : Fin (m + 1) → Ω) (y : Ω) :
    linearMarkovAppendFinitePath past (fun _ : Fin 1 => y) =
      (Fin.snoc past y : Fin ((m + 1) + 1) → Ω) := by
  exact Fin.append_right_eq_snoc past (fun _ : Fin 1 => y)

/-- Extending the future and then concatenating equals extending the already
concatenated path. -/
@[simp] theorem linearMarkovAppendFinitePath_snoc
    {Ω : Type*} {m n : ℕ}
    (past : Fin (m + 1) → Ω)
    (future : Fin (n + 1) → Ω)
    (y : Ω) :
    linearMarkovAppendFinitePath past (Fin.snoc future y) =
      Fin.snoc (linearMarkovAppendFinitePath past future) y := by
  exact Fin.append_snoc past future y

/-- The terminal state of a concatenated path is the terminal state of its
strictly-positive future. -/
@[simp] theorem linearMarkovAppendFinitePath_last
    {Ω : Type*} {m n : ℕ}
    (past : Fin (m + 1) → Ω)
    (future : Fin (n + 1) → Ω) :
    linearMarkovAppendFinitePath past future (Fin.last ((m + 1) + n)) =
      future (Fin.last n) := by
  simpa [linearMarkovAppendFinitePath] using
    (Fin.append_right past future (Fin.last n))

/-- The law obtained by sampling a finite prefix and then an independent
conditional continuation from its terminal state. -/
def linearMarkovFinitePathSplitPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (m n : ℕ) :
    PMF (Fin (((m + 1) + n) + 1) → Ω) :=
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
        (transition (path (Fin.last ((m + 1) + n)))).map fun y =>
          Fin.snoc path y := by
  unfold linearMarkovFinitePathSplitPMF
    linearMarkovPositiveTimeFuturePMF
  change
    (linearMarkovFinitePathPMF initial transition m).bind
        (fun past =>
          ((linearMarkovFinitePathPMF
              (transition (past (Fin.last m))) transition n).bind
            (fun future =>
              (transition (future (Fin.last n))).map fun y =>
                Fin.snoc future y)).map
            (linearMarkovAppendFinitePath past)) =
      ((linearMarkovFinitePathPMF initial transition m).bind
        (fun past =>
          (linearMarkovFinitePathPMF
              (transition (past (Fin.last m))) transition n).map
            (linearMarkovAppendFinitePath past))).bind
        (fun path =>
          (transition (path (Fin.last ((m + 1) + n)))).map fun y =>
            Fin.snoc path y)
  rw [PMF.bind_bind]
  apply congrArg (PMF.bind (linearMarkovFinitePathPMF initial transition m))
  funext past
  rw [PMF.map_bind, PMF.bind_map]
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
      linearMarkovFinitePathPMF initial transition ((m + 1) + n) := by
  induction n with
  | zero =>
      unfold linearMarkovFinitePathSplitPMF
        linearMarkovPositiveTimeFuturePMF
      change
        (linearMarkovFinitePathPMF initial transition m).bind
            (fun past =>
              ((transition (past (Fin.last m))).map
                (fun y => fun _ : Fin 1 => y)).map
                  (linearMarkovAppendFinitePath past)) =
          (linearMarkovFinitePathPMF initial transition m).bind
            (fun past =>
              (transition (past (Fin.last m))).map fun y =>
                Fin.snoc past y)
      apply congrArg (PMF.bind (linearMarkovFinitePathPMF initial transition m))
      funext past
      rw [PMF.map_comp]
      simp only [Function.comp_apply]
      congr 1
      funext y
      simp
  | succ n ih =>
      rw [linearMarkovFinitePathSplitPMF_succ, ih]
      rfl

/-- Packing a single-chain centered decomposition into the sum-indexed
chronological carrier simply concatenates its past and positive continuation. -/
theorem linearMarkovCenteredFinitePathToChronologicalSum_singleChain
    {Ω : Type*} {n : ℕ}
    (past : Fin (n + 2) → Ω)
    (positive : LinearMarkovPositiveTimeFuturePath Ω n) :
    linearMarkovCenteredFinitePathToChronologicalSum
        (linearMarkovSingleChainCenteredFinitePath past positive) =
      linearMarkovAppendFinitePath past positive := by
  unfold linearMarkovCenteredFinitePathToChronologicalSum
    linearMarkovSingleChainCenteredFinitePath
  rw [linearMarkovSingleChainPastOfCenteredSplit]
  rfl

/-- The sum-indexed chronological law before arithmetic normalization. -/
def linearMarkovChronologicalCenteredFinitePathSumPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    PMF (LinearMarkovChronologicalCenteredFinitePathSum Ω n) :=
  (linearMarkovSingleChainCenteredFinitePathPMF initial transition n).map
    linearMarkovCenteredFinitePathToChronologicalSum

/-- The sum-indexed chronological law is exactly the generic prefix/future
split law. -/
theorem linearMarkovChronologicalCenteredFinitePathSumPMF_eq_split
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    linearMarkovChronologicalCenteredFinitePathSumPMF initial transition n =
      linearMarkovFinitePathSplitPMF initial transition (n + 1) n := by
  unfold linearMarkovChronologicalCenteredFinitePathSumPMF
    linearMarkovSingleChainCenteredFinitePathPMF
    linearMarkovFinitePathSplitPMF
  rw [PMF.map_bind]
  apply congrArg
    (PMF.bind (linearMarkovFinitePathPMF initial transition (n + 1)))
  funext past
  rw [PMF.map_comp]
  simp only [Function.comp_apply]
  congr 1
  funext positive
  exact linearMarkovCenteredFinitePathToChronologicalSum_singleChain past positive

/-- Therefore the sum-indexed chronological centered law is one ordinary finite
Markov path law. -/
theorem linearMarkovChronologicalCenteredFinitePathSumPMF_eq_finitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    linearMarkovChronologicalCenteredFinitePathSumPMF initial transition n =
      linearMarkovFinitePathPMF initial transition ((n + 2) + n) := by
  rw [linearMarkovChronologicalCenteredFinitePathSumPMF_eq_split]
  exact linearMarkovFinitePathSplitPMF_eq_finitePathPMF
    initial transition (n + 1) n

/-- Reindex a finite path when two transition counts are propositionally equal. -/
def linearMarkovFinitePathReindex
    {Ω : Type*} {a b : ℕ}
    (h : a = b)
    (path : Fin (a + 1) → Ω) :
    Fin (b + 1) → Ω :=
  path ∘ Fin.cast (congrArg (fun k => k + 1) h).symm

/-- Reindexing an entire finite-path PMF along an equality of horizons changes
only its carrier representation. -/
theorem linearMarkovFinitePathPMF_map_reindex
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    {a b : ℕ}
    (h : a = b) :
    (linearMarkovFinitePathPMF initial transition a).map
        (linearMarkovFinitePathReindex h) =
      linearMarkovFinitePathPMF initial transition b := by
  subst b
  simpa [linearMarkovFinitePathReindex, Function.comp_def] using
    PMF.map_id (linearMarkovFinitePathPMF initial transition a)

/-- The explicit chronological centered law is exactly one ordinary finite
Markov path law.  Detailed balance is not needed for this identity. -/
theorem linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    linearMarkovChronologicalCenteredFinitePathPMF initial transition n =
      linearMarkovFinitePathPMF initial transition (2 * n + 2) := by
  let h : (n + 2) + n = 2 * n + 2 := by omega
  unfold linearMarkovChronologicalCenteredFinitePathPMF
  calc
    (linearMarkovSingleChainCenteredFinitePathPMF initial transition n).map
        linearMarkovCenteredFinitePathToChronological =
      ((linearMarkovSingleChainCenteredFinitePathPMF initial transition n).map
        linearMarkovCenteredFinitePathToChronologicalSum).map
          linearMarkovChronologicalSumToExplicit := by
            rw [PMF.map_comp]
            rfl
    _ = (linearMarkovFinitePathPMF initial transition ((n + 2) + n)).map
          linearMarkovChronologicalSumToExplicit := by
            rw [linearMarkovChronologicalCenteredFinitePathSumPMF_eq_finitePathPMF]
    _ = linearMarkovFinitePathPMF initial transition (2 * n + 2) := by
          simpa [linearMarkovChronologicalSumToExplicit,
            linearMarkovFinitePathReindex] using
            (linearMarkovFinitePathPMF_map_reindex
              initial transition h)

end

end MathlibAnalytic
end MGAP4D
