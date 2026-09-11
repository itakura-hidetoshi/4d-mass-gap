import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Deleting the terminal coordinate of a conditional positive-time future gives
the shorter conditional future law. -/
theorem linearMarkovPositiveTimeFuturePMF_succ_map_init
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω) :
    (linearMarkovPositiveTimeFuturePMF transition (n + 1) boundary).map
        Fin.init =
      linearMarkovPositiveTimeFuturePMF transition n boundary := by
  unfold linearMarkovPositiveTimeFuturePMF
  exact linearMarkovFinitePathPMF_succ_map_init
    (transition boundary) transition n

/-- Remove the outermost negative-time and positive-time coordinates while
keeping the time-zero boundary fixed. -/
def linearMarkovCenteredFinitePathInit
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω (n + 1)) :
    LinearMarkovCenteredFinitePath Ω n :=
  ⟨Fin.init path.negative, path.boundary, Fin.init path.positive⟩

/-- Boundary-conditioned centered laws are consistent under simultaneous
terminal truncation of their two future copies. -/
theorem linearMarkovCenteredFinitePathConditionalPMF_succ_map_init
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω) :
    (linearMarkovCenteredFinitePathConditionalPMF transition (n + 1) boundary).map
        linearMarkovCenteredFinitePathInit =
      linearMarkovCenteredFinitePathConditionalPMF transition n boundary := by
  let qBig := linearMarkovPositiveTimeFuturePMF transition (n + 1) boundary
  let qSmall := linearMarkovPositiveTimeFuturePMF transition n boundary
  have hq : qBig.map Fin.init = qSmall := by
    exact linearMarkovPositiveTimeFuturePMF_succ_map_init
      transition n boundary
  unfold linearMarkovCenteredFinitePathConditionalPMF
    linearMarkovCenteredFinitePathInit
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  change
    qBig.bind (fun negative =>
      qBig.map (fun positive =>
        (⟨Fin.init negative, boundary, Fin.init positive⟩ :
          LinearMarkovCenteredFinitePath Ω n))) =
      qSmall.bind (fun negative =>
        qSmall.map (fun positive =>
          (⟨negative, boundary, positive⟩ :
            LinearMarkovCenteredFinitePath Ω n)))
  rw [← hq]
  rw [PMF.bind_map]
  apply congrArg (PMF.bind qBig)
  funext negative
  simp only [Function.comp_apply]
  rw [PMF.map_comp]
  rfl

/-- Full centered finite path laws form a projectively consistent family under
simultaneous removal of the two outermost time coordinates. -/
theorem linearMarkovCenteredFinitePathPMF_succ_map_init
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovCenteredFinitePathPMF initial transition (n + 1)).map
        linearMarkovCenteredFinitePathInit =
      linearMarkovCenteredFinitePathPMF initial transition n := by
  unfold linearMarkovCenteredFinitePathPMF
  rw [PMF.map_bind]
  apply congrArg (PMF.bind initial)
  funext boundary
  exact linearMarkovCenteredFinitePathConditionalPMF_succ_map_init
    transition n boundary

/-- The chronological centered cut removes the oldest negative-time coordinate
and the latest positive-time coordinate.  It is defined by conjugating the
centered truncation through the explicit chronological equivalence. -/
def linearMarkovChronologicalCenteredFinitePathInit
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePath Ω (n + 1)) :
    LinearMarkovChronologicalCenteredFinitePath Ω n :=
  linearMarkovCenteredFinitePathToChronological
    (linearMarkovCenteredFinitePathInit
      (linearMarkovChronologicalToCenteredFinitePath path))

/-- Chronological packing commutes exactly with the centered outer-coordinate
cut. -/
@[simp] theorem linearMarkovChronologicalCenteredFinitePathInit_pack
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω (n + 1)) :
    linearMarkovChronologicalCenteredFinitePathInit
        (linearMarkovCenteredFinitePathToChronological path) =
      linearMarkovCenteredFinitePathToChronological
        (linearMarkovCenteredFinitePathInit path) := by
  simp [linearMarkovChronologicalCenteredFinitePathInit]

/-- Under detailed balance, the explicit chronological single-chain path laws
are projectively consistent when the two outermost coordinates are removed. -/
theorem linearMarkovChronologicalCenteredFinitePathPMF_succ_map_init_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovChronologicalCenteredFinitePathPMF
        initial transition (n + 1)).map
          linearMarkovChronologicalCenteredFinitePathInit =
      linearMarkovChronologicalCenteredFinitePathPMF
        initial transition n := by
  unfold linearMarkovChronologicalCenteredFinitePathPMF
  rw [linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
      initial transition hdb (n + 1),
    linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
      initial transition hdb n]
  calc
    ((linearMarkovCenteredFinitePathPMF initial transition (n + 1)).map
        linearMarkovCenteredFinitePathToChronological).map
          linearMarkovChronologicalCenteredFinitePathInit =
      ((linearMarkovCenteredFinitePathPMF initial transition (n + 1)).map
        linearMarkovCenteredFinitePathInit).map
          linearMarkovCenteredFinitePathToChronological := by
            rw [PMF.map_comp, PMF.map_comp]
            apply congrArg
              (fun f =>
                (linearMarkovCenteredFinitePathPMF
                  initial transition (n + 1)).map f)
            funext path
            exact linearMarkovChronologicalCenteredFinitePathInit_pack path
    _ = (linearMarkovCenteredFinitePathPMF initial transition n).map
          linearMarkovCenteredFinitePathToChronological := by
            rw [linearMarkovCenteredFinitePathPMF_succ_map_init]

end

end MathlibAnalytic
end MGAP4D
