import MGAP4D.MathlibAnalytic.LinearMarkovSingleChainCenteredTimeReflectionPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Shift a two-sided integer-time path by `k`, with
`(τₖ path)(t) = path(t + k)`. -/
def linearMarkovIntegerPathShift
    {Ω : Type*} (k : ℤ) (path : ℤ → Ω) : ℤ → Ω :=
  fun t => path (t + k)

@[simp] theorem linearMarkovIntegerPathShift_apply
    {Ω : Type*} (k t : ℤ) (path : ℤ → Ω) :
    linearMarkovIntegerPathShift k path t = path (t + k) :=
  rfl

@[simp] theorem linearMarkovIntegerPathShift_zero
    {Ω : Type*} (path : ℤ → Ω) :
    linearMarkovIntegerPathShift 0 path = path := by
  funext t
  simp [linearMarkovIntegerPathShift]

/-- Integer-time shifts compose by addition of their displacements. -/
theorem linearMarkovIntegerPathShift_add
    {Ω : Type*} (k l : ℤ) (path : ℤ → Ω) :
    linearMarkovIntegerPathShift k
        (linearMarkovIntegerPathShift l path) =
      linearMarkovIntegerPathShift (k + l) path := by
  funext t
  simp [linearMarkovIntegerPathShift, add_assoc]

@[simp] theorem linearMarkovIntegerPathShift_neg_left
    {Ω : Type*} (k : ℤ) (path : ℤ → Ω) :
    linearMarkovIntegerPathShift (-k)
        (linearMarkovIntegerPathShift k path) = path := by
  rw [linearMarkovIntegerPathShift_add]
  simp

@[simp] theorem linearMarkovIntegerPathShift_neg_right
    {Ω : Type*} (k : ℤ) (path : ℤ → Ω) :
    linearMarkovIntegerPathShift k
        (linearMarkovIntegerPathShift (-k) path) = path := by
  rw [linearMarkovIntegerPathShift_add]
  simp

/-- Integer-time shift as an equivalence of the full path carrier. -/
def linearMarkovIntegerPathShiftEquiv
    (Ω : Type*) (k : ℤ) : (ℤ → Ω) ≃ (ℤ → Ω) where
  toFun := linearMarkovIntegerPathShift k
  invFun := linearMarkovIntegerPathShift (-k)
  left_inv := linearMarkovIntegerPathShift_neg_left k
  right_inv := linearMarkovIntegerPathShift_neg_right k

/-- Integer-time shift is measurable for the product measurable space. -/
theorem linearMarkovIntegerPathShift_measurable
    {Ω : Type*} [MeasurableSpace Ω] (k : ℤ) :
    Measurable (@linearMarkovIntegerPathShift Ω k) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply (t + k))

/-- The inverse integer-time shift is measurable as well. -/
theorem linearMarkovIntegerPathShiftEquiv_inv_measurable
    {Ω : Type*} [MeasurableSpace Ω] (k : ℤ) :
    Measurable (linearMarkovIntegerPathShiftEquiv Ω k).invFun := by
  exact linearMarkovIntegerPathShift_measurable (-k)

/-- The second marginal of the one-step path law is the initial law followed by
one application of the transition kernel. -/
theorem linearMarkovPairPMF_map_snd_eq_bind
    {Ω : Type*}
    (initial : PMF Ω) (transition : Ω → PMF Ω) :
    (linearMarkovPairPMF initial transition).map Prod.snd =
      initial.bind transition := by
  unfold linearMarkovPairPMF
  rw [PMF.map_bind]
  apply congrArg (PMF.bind initial)
  funext x
  rw [PMF.map_comp]
  simpa [Function.comp_def] using PMF.map_id (transition x)

/-- Detailed balance makes one transition preserve the initial PMF exactly. -/
theorem linearMarkovInitialPMF_bind_transition_of_detailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    initial.bind transition = initial := by
  rw [← linearMarkovPairPMF_map_snd_eq_bind]
  exact linearMarkovPairPMF_map_snd_of_detailedBalanceReal
    initial transition hdb

/-- Mixing finite path laws whose initial PMFs are the one-step transition laws
is the same as starting the path from the mixed one-step marginal. -/
theorem linearMarkovFinitePathPMF_bind_transition_initial
    {Ω : Type*}
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (n : ℕ) :
    initial.bind
        (fun x => linearMarkovFinitePathPMF (transition x) transition n) =
      linearMarkovFinitePathPMF (initial.bind transition) transition n := by
  induction n with
  | zero =>
      rw [linearMarkovFinitePathPMF]
      rw [PMF.bind_map]
  | succ n ih =>
      rw [linearMarkovFinitePathPMF]
      rw [PMF.bind_bind]
      rw [ih]

/-- Deleting the first coordinate of a finite Markov path advances its initial
law by one application of the transition kernel. -/
theorem linearMarkovFinitePathPMF_succ_map_tail
    {Ω : Type*}
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition (n + 1)).map Fin.tail =
      linearMarkovFinitePathPMF (initial.bind transition) transition n := by
  rw [linearMarkovFinitePathPMF_eq_initial_bind_positiveTimeFuture]
  rw [PMF.map_bind]
  change
    initial.bind (fun boundary =>
      ((linearMarkovFinitePathPMF (transition boundary) transition n).map
          (fun future => Fin.cons boundary future)).map Fin.tail) =
      linearMarkovFinitePathPMF (initial.bind transition) transition n
  calc
    _ = initial.bind
        (fun boundary =>
          linearMarkovFinitePathPMF (transition boundary) transition n) := by
            apply congrArg (PMF.bind initial)
            funext boundary
            rw [PMF.map_comp]
            simpa [Function.comp_def] using
              PMF.map_id
                (linearMarkovFinitePathPMF
                  (transition boundary) transition n)
    _ = linearMarkovFinitePathPMF
          (initial.bind transition) transition n :=
      linearMarkovFinitePathPMF_bind_transition_initial
        initial transition n

/-- Under detailed balance, deleting the first coordinate leaves every finite
path law unchanged after the natural horizon reduction. -/
theorem linearMarkovFinitePathPMF_succ_map_tail_of_detailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition (n + 1)).map Fin.tail =
      linearMarkovFinitePathPMF initial transition n := by
  rw [linearMarkovFinitePathPMF_succ_map_tail]
  rw [linearMarkovInitialPMF_bind_transition_of_detailedBalanceReal
    initial transition hdb]

end

end MathlibAnalytic
end MGAP4D
