import MGAP4D.MathlibAnalytic.LinearMarkovInfinitePathMeasure
import MGAP4D.MathlibAnalytic.LinearMarkovFiniteDimensionalPMFStationarity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Finset MeasureTheory Preorder

noncomputable section

/-- Delete the initial coordinate of a finite path tuple. -/
def linearMarkovFinitePathTail
    {Ω : Type*}
    {n : ℕ} :
    (Fin (n + 2) → Ω) → (Fin (n + 1) → Ω) :=
  Fin.tail

/-- Deleting the first coordinate commutes with appending a new terminal
coordinate. -/
theorem linearMarkovFinitePathTail_snoc
    {Ω : Type*}
    (n : ℕ)
    (path : Fin (n + 2) → Ω)
    (y : Ω) :
    linearMarkovFinitePathTail (n := n + 1) (Fin.snoc path y) =
      Fin.snoc (linearMarkovFinitePathTail (n := n) path) y := by
  funext i
  unfold linearMarkovFinitePathTail
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.tail]
  · change path j.succ = path j.succ
    rfl

/-- Under stationarity of the initial law, deleting the initial coordinate of a
finite Markov path gives exactly the preceding finite path law. -/
theorem linearMarkovFinitePathPMF_succ_map_tail_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition (n + 1)).map
        (linearMarkovFinitePathTail (n := n)) =
      linearMarkovFinitePathPMF initial transition n := by
  induction n with
  | zero =>
      calc
        (linearMarkovFinitePathPMF initial transition 1).map
            (linearMarkovFinitePathTail (n := 0)) =
          ((linearMarkovFinitePathPMF initial transition 1).map
              (fun path => path (Fin.last 1))).map
            (fun x _ => x) := by
              rw [PMF.map_comp]
              congr 1
              funext path i
              fin_cases i
              rfl
        _ = initial.map (fun x _ => x) := by
          rw [linearMarkovFinitePathPMF_map_last_of_expectation_stationary
            initial transition hstationary 1]
        _ = linearMarkovFinitePathPMF initial transition 0 := by
          rfl
  | succ n ih =>
      rw [linearMarkovFinitePathPMF, PMF.map_bind]
      simp_rw [PMF.map_comp]
      have hKernel :
          (fun path : Fin (n + 2) → Ω =>
            (transition (path (Fin.last (n + 1)))).map
              (linearMarkovFinitePathTail (n := n + 1) ∘
                fun y => Fin.snoc path y)) =
            (fun path : Fin (n + 2) → Ω =>
              (transition ((linearMarkovFinitePathTail (n := n) path)
                (Fin.last n))).map
                (fun y => Fin.snoc
                  (linearMarkovFinitePathTail (n := n) path) y)) := by
        funext path
        have hLast :
            path (Fin.last (n + 1)) =
              (linearMarkovFinitePathTail (n := n) path) (Fin.last n) := by
          rfl
        rw [hLast]
        congr 1
        funext y
        exact linearMarkovFinitePathTail_snoc n path y
      rw [hKernel]
      let k : (Fin (n + 1) → Ω) → PMF (Fin (n + 2) → Ω) :=
        fun path =>
          (transition (path (Fin.last n))).map fun y => Fin.snoc path y
      change
        (linearMarkovFinitePathPMF initial transition (n + 1)).bind
            (k ∘ linearMarkovFinitePathTail (n := n)) =
          linearMarkovFinitePathPMF initial transition (n + 1)
      rw [← PMF.bind_map]
      rw [ih]
      rfl

/-- The left shift on natural-time paths. -/
def linearMarkovPathShift
    {Ω : Type*} :
    (ℕ → Ω) → (ℕ → Ω) :=
  fun path i => path (i + 1)

/-- The natural-time path shift is measurable. -/
theorem measurable_linearMarkovPathShift
    {Ω : Type*} [MeasurableSpace Ω] :
    Measurable (linearMarkovPathShift (Ω := Ω)) := by
  unfold linearMarkovPathShift
  fun_prop

/-- Every finite prefix of the shifted infinite path law is the original finite
path law when the initial PMF is stationary. -/
theorem linearMarkovInfinitePathMeasure_map_shift_map_finPrefix
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f)
    (n : ℕ) :
    ((linearMarkovInfinitePathMeasure initial transition).map
        linearMarkovPathShift).map
          (linearMarkovInfinitePathFinPrefix n) =
      (linearMarkovFinitePathPMF initial transition n).toMeasure := by
  have hShiftMeasurable :
      Measurable (linearMarkovPathShift (Ω := Ω)) :=
    measurable_linearMarkovPathShift
  have hPrefixMeasurable :
      Measurable (linearMarkovInfinitePathFinPrefix (Ω := Ω) n) :=
    measurable_linearMarkovInfinitePathFinPrefix n
  have hLongPrefixMeasurable :
      Measurable (linearMarkovInfinitePathFinPrefix (Ω := Ω) (n + 1)) :=
    measurable_linearMarkovInfinitePathFinPrefix (n + 1)
  have hTailMeasurable :
      Measurable (linearMarkovFinitePathTail
        (Ω := Ω) (n := n)) :=
    measurable_of_finite _
  have hComp :
      linearMarkovInfinitePathFinPrefix (Ω := Ω) n ∘
          linearMarkovPathShift =
        linearMarkovFinitePathTail (n := n) ∘
          linearMarkovInfinitePathFinPrefix (n + 1) := by
    funext path i
    rfl
  calc
    ((linearMarkovInfinitePathMeasure initial transition).map
        linearMarkovPathShift).map
          (linearMarkovInfinitePathFinPrefix n) =
      (linearMarkovInfinitePathMeasure initial transition).map
        (linearMarkovInfinitePathFinPrefix n ∘
          linearMarkovPathShift) :=
            Measure.map_map hPrefixMeasurable hShiftMeasurable
    _ = (linearMarkovInfinitePathMeasure initial transition).map
        (linearMarkovFinitePathTail (n := n) ∘
          linearMarkovInfinitePathFinPrefix (n + 1)) := by
            rw [hComp]
    _ = ((linearMarkovInfinitePathMeasure initial transition).map
          (linearMarkovInfinitePathFinPrefix (n + 1))).map
        (linearMarkovFinitePathTail (n := n)) := by
          symm
          exact Measure.map_map hTailMeasurable hLongPrefixMeasurable
    _ = (linearMarkovFinitePathPMF initial transition (n + 1)).toMeasure.map
        (linearMarkovFinitePathTail (n := n)) := by
          rw [linearMarkovInfinitePathMeasure_map_finPrefix]
    _ = ((linearMarkovFinitePathPMF initial transition (n + 1)).map
        (linearMarkovFinitePathTail (n := n))).toMeasure :=
          PMF.toMeasure_map
            (linearMarkovFinitePathTail (n := n))
            (linearMarkovFinitePathPMF initial transition (n + 1))
            hTailMeasurable
    _ = (linearMarkovFinitePathPMF initial transition n).toMeasure :=
      congrArg PMF.toMeasure
        (linearMarkovFinitePathPMF_succ_map_tail_of_expectation_stationary
          initial transition hstationary n)

/-- A stationary finite-state Markov path measure is invariant under the full
left shift on path space. -/
theorem linearMarkovInfinitePathMeasure_map_shift_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f) :
    (linearMarkovInfinitePathMeasure initial transition).map
        linearMarkovPathShift =
      linearMarkovInfinitePathMeasure initial transition := by
  let P := linearMarkovFinitePathProjectiveFamily initial transition
  have hP :
      IsProjectiveMeasureFamily (α := fun _ : ℕ => Ω) P :=
    linearMarkovFinitePathProjectiveFamily_projective initial transition
  have hOriginal :
      IsProjectiveLimit
        (linearMarkovInfinitePathMeasure initial transition) P := by
    unfold linearMarkovInfinitePathMeasure
    exact isProjectiveLimit_standardBorelKolmogorovProjectiveLimit hP
  have hShifted :
      IsProjectiveLimit
        ((linearMarkovInfinitePathMeasure initial transition).map
          linearMarkovPathShift) P := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff
      (X := fun _ : ℕ => Ω) hP]
    intro n
    have hIic :
        frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n =
          linearMarkovFinIicPathEquiv (Ω := Ω) n ∘
            linearMarkovInfinitePathFinPrefix n := by
      funext path i
      rfl
    have hEquivMeasurable :
        Measurable (linearMarkovFinIicPathEquiv (Ω := Ω) n) :=
      measurable_of_finite _
    rw [hIic]
    calc
      ((linearMarkovInfinitePathMeasure initial transition).map
          linearMarkovPathShift).map
          (linearMarkovFinIicPathEquiv n ∘
            linearMarkovInfinitePathFinPrefix n) =
        (((linearMarkovInfinitePathMeasure initial transition).map
          linearMarkovPathShift).map
            (linearMarkovInfinitePathFinPrefix n)).map
          (linearMarkovFinIicPathEquiv n) := by
            symm
            exact Measure.map_map hEquivMeasurable
              (measurable_linearMarkovInfinitePathFinPrefix n)
      _ = (linearMarkovFinitePathPMF initial transition n).toMeasure.map
          (linearMarkovFinIicPathEquiv n) := by
            rw [linearMarkovInfinitePathMeasure_map_shift_map_finPrefix
              initial transition hstationary n]
      _ = (linearMarkovFiniteIicPathPMF initial transition n).toMeasure := by
        unfold linearMarkovFiniteIicPathPMF
        exact PMF.toMeasure_map
          (linearMarkovFinIicPathEquiv n)
          (linearMarkovFinitePathPMF initial transition n)
          hEquivMeasurable
      _ = P (Finset.Iic n) := by
        unfold P linearMarkovFinitePathProjectiveFamily
        symm
        exact MeasureTheory.inducedFamily_Iic
          (X := fun _ : ℕ => Ω)
          (linearMarkovFiniteIicPathMeasure initial transition) n
  exact IsProjectiveLimit.unique hShifted hOriginal

end

end MathlibAnalytic
end MGAP4D