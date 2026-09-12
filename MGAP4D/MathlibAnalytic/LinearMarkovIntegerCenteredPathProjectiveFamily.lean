import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathConsistency
import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathFinitePathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit chronological carrier, now viewed as the symmetric integer
interval `[-n-1, n+1]`. -/
abbrev LinearMarkovIntegerCenteredFinitePath
    (Ω : Type*) (n : ℕ) :=
  LinearMarkovChronologicalCenteredFinitePath Ω n

/-- Integer time carried by a coordinate of the explicit chronological tuple. -/
def linearMarkovIntegerCenteredTime
    {n : ℕ} (i : Fin (2 * n + 3)) : ℤ :=
  (i.1 : ℤ) - ((n + 1 : ℕ) : ℤ)

/-- Every explicit coordinate lies above the left endpoint `-n-1`. -/
theorem linearMarkovIntegerCenteredTime_lower
    {n : ℕ} (i : Fin (2 * n + 3)) :
    -((n + 1 : ℕ) : ℤ) ≤ linearMarkovIntegerCenteredTime i := by
  unfold linearMarkovIntegerCenteredTime
  omega

/-- Every explicit coordinate lies below the right endpoint `n+1`. -/
theorem linearMarkovIntegerCenteredTime_upper
    {n : ℕ} (i : Fin (2 * n + 3)) :
    linearMarkovIntegerCenteredTime i ≤ ((n + 1 : ℕ) : ℤ) := by
  unfold linearMarkovIntegerCenteredTime
  have hi := i.2
  omega

/-- The center coordinate of the symmetric integer interval. -/
def linearMarkovIntegerCenteredZeroIndex (n : ℕ) : Fin (2 * n + 3) :=
  ⟨n + 1, by omega⟩

@[simp] theorem linearMarkovIntegerCenteredTime_zeroIndex
    (n : ℕ) :
    linearMarkovIntegerCenteredTime
        (linearMarkovIntegerCenteredZeroIndex n) = 0 := by
  simp [linearMarkovIntegerCenteredTime,
    linearMarkovIntegerCenteredZeroIndex]

@[simp] theorem linearMarkovIntegerCenteredTime_first
    (n : ℕ) :
    linearMarkovIntegerCenteredTime (0 : Fin (2 * n + 3)) =
      -((n + 1 : ℕ) : ℤ) := by
  simp [linearMarkovIntegerCenteredTime]

@[simp] theorem linearMarkovIntegerCenteredTime_last
    (n : ℕ) :
    linearMarkovIntegerCenteredTime (Fin.last (2 * n + 2)) =
      ((n + 1 : ℕ) : ℤ) := by
  simp [linearMarkovIntegerCenteredTime]
  omega

/-- The finite coordinate labeling by integer time is injective. -/
theorem linearMarkovIntegerCenteredTime_injective
    (n : ℕ) :
    Function.Injective
      (@linearMarkovIntegerCenteredTime n) := by
  intro i j hij
  apply Fin.ext
  unfold linearMarkovIntegerCenteredTime at hij
  omega

/-- Complete tuple reversal realizes integer time reflection `t ↦ -t`. -/
theorem linearMarkovIntegerCenteredTime_rev
    {n : ℕ} (i : Fin (2 * n + 3)) :
    linearMarkovIntegerCenteredTime i.rev =
      -linearMarkovIntegerCenteredTime i := by
  unfold linearMarkovIntegerCenteredTime
  simp
  omega

/-- The Gibbs/initial-started law on the symmetric integer interval
`[-n-1, n+1]`. -/
abbrev linearMarkovIntegerCenteredFinitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    PMF (LinearMarkovIntegerCenteredFinitePath Ω n) :=
  linearMarkovChronologicalCenteredFinitePathPMF initial transition n

/-- Restrict the symmetric interval of radius `n+d+1` to radius `n+1` by
removing the two outermost coordinates `d` times. -/
def linearMarkovIntegerCenteredFinitePathRestrictBy
    {Ω : Type*} (n : ℕ) :
    (d : ℕ) →
      LinearMarkovIntegerCenteredFinitePath Ω (n + d) →
        LinearMarkovIntegerCenteredFinitePath Ω n
  | 0 => id
  | d + 1 => fun path =>
      linearMarkovIntegerCenteredFinitePathRestrictBy n d
        (linearMarkovChronologicalCenteredFinitePathInit path)

@[simp] theorem linearMarkovIntegerCenteredFinitePathRestrictBy_zero
    {Ω : Type*} (n : ℕ)
    (path : LinearMarkovIntegerCenteredFinitePath Ω n) :
    linearMarkovIntegerCenteredFinitePathRestrictBy n 0 path = path :=
  rfl

@[simp] theorem linearMarkovIntegerCenteredFinitePathRestrictBy_succ
    {Ω : Type*} (n d : ℕ)
    (path : LinearMarkovIntegerCenteredFinitePath Ω (n + (d + 1))) :
    linearMarkovIntegerCenteredFinitePathRestrictBy n (d + 1) path =
      linearMarkovIntegerCenteredFinitePathRestrictBy n d
        (linearMarkovChronologicalCenteredFinitePathInit path) :=
  rfl

/-- The arbitrary-radius restriction is the recursive composition of the
one-step outer-coordinate cuts. -/
theorem linearMarkovIntegerCenteredFinitePathRestrictBy_succ_comp
    {Ω : Type*} (n d : ℕ) :
    @linearMarkovIntegerCenteredFinitePathRestrictBy Ω n (d + 1) =
      linearMarkovIntegerCenteredFinitePathRestrictBy n d ∘
        linearMarkovChronologicalCenteredFinitePathInit := by
  rfl

/-- Under detailed balance, every larger symmetric integer interval restricts
exactly to every smaller one. -/
theorem linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n d : ℕ) :
    (linearMarkovIntegerCenteredFinitePathPMF
        initial transition (n + d)).map
      (linearMarkovIntegerCenteredFinitePathRestrictBy n d) =
        linearMarkovIntegerCenteredFinitePathPMF
          initial transition n := by
  induction d with
  | zero =>
      exact PMF.map_id
        (linearMarkovIntegerCenteredFinitePathPMF initial transition n)
  | succ d ih =>
      change
        (linearMarkovChronologicalCenteredFinitePathPMF
            initial transition ((n + d) + 1)).map
          (linearMarkovIntegerCenteredFinitePathRestrictBy n d ∘
            linearMarkovChronologicalCenteredFinitePathInit) =
          linearMarkovChronologicalCenteredFinitePathPMF
            initial transition n
      rw [← PMF.map_comp]
      rw [linearMarkovChronologicalCenteredFinitePathPMF_succ_map_init_of_detailedBalance
        initial transition hdb (n + d)]
      exact ih

/-- The same projective restriction statement transported to the ordinary
finite Markov path PMFs of transition horizon `2*n+2`. -/
theorem linearMarkovFinitePathPMF_map_integerCenteredRestrictBy_of_detailedBalance
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n d : ℕ) :
    (linearMarkovFinitePathPMF initial transition (2 * (n + d) + 2)).map
      (linearMarkovIntegerCenteredFinitePathRestrictBy n d) =
        linearMarkovFinitePathPMF initial transition (2 * n + 2) := by
  rw [← linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
      initial transition (n + d),
    ← linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
      initial transition n]
  exact
    linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
      initial transition hdb n d

end

end MathlibAnalytic
end MGAP4D
