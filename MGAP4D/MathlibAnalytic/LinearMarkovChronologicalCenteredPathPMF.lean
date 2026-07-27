import MGAP4D.MathlibAnalytic.LinearMarkovSingleChainCenteredTimeReflectionPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A centered finite path written in chronological order
`X₋ₙ₋₁, ..., X₋₁, X₀, X₁, ..., Xₙ₊₁`. -/
abbrev LinearMarkovChronologicalCenteredFinitePath
    (Ω : Type*) (n : ℕ) :=
  Fin (2 * n + 3) → Ω

/-- The same chronological carrier before normalizing its length arithmetic. -/
abbrev LinearMarkovChronologicalCenteredFinitePathSum
    (Ω : Type*) (n : ℕ) :=
  Fin ((n + 2) + (n + 1)) → Ω

/-- Pack a reflected-future centered path into one chronological finite tuple,
before normalizing the tuple length to `2 * n + 3`. -/
def linearMarkovCenteredFinitePathToChronologicalSum
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω n) :
    LinearMarkovChronologicalCenteredFinitePathSum Ω n :=
  Fin.append
    (linearMarkovFinitePathReverse (Fin.cons path.boundary path.negative))
    path.positive

/-- Split one chronological finite tuple into its reflected negative half,
time-zero boundary, and positive half. -/
def linearMarkovChronologicalSumToCenteredFinitePath
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePathSum Ω n) :
    LinearMarkovCenteredFinitePath Ω n :=
  linearMarkovSingleChainCenteredFinitePath
    (fun i => path (Fin.castAdd (n + 1) i))
    (fun i => path (Fin.natAdd (n + 2) i))

/-- Reconstructing a centered path after chronological packing is exact. -/
@[simp] theorem linearMarkovChronologicalSumToCenteredFinitePath_pack
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω n) :
    linearMarkovChronologicalSumToCenteredFinitePath
        (linearMarkovCenteredFinitePathToChronologicalSum path) = path := by
  rcases path with ⟨negative, boundary, positive⟩
  simpa [linearMarkovChronologicalSumToCenteredFinitePath,
    linearMarkovCenteredFinitePathToChronologicalSum] using
      (linearMarkovSingleChainCenteredFinitePath_reverse_cons
        boundary negative positive)

/-- Reversing the boundary/reflected-past reconstruction recovers the original
chronological past segment. -/
@[simp] theorem linearMarkovSingleChainPastOfCenteredSplit
    {Ω : Type*} {n : ℕ}
    (past : Fin (n + 2) → Ω) :
    linearMarkovFinitePathReverse
        (Fin.cons (past (Fin.last (n + 1)))
          (linearMarkovSingleChainReflectedPast past)) = past := by
  have hzero :
      linearMarkovFinitePathReverse past 0 = past (Fin.last (n + 1)) := by
    simp [linearMarkovFinitePathReverse]
  have hcons :
      Fin.cons (past (Fin.last (n + 1)))
          (linearMarkovSingleChainReflectedPast past) =
        linearMarkovFinitePathReverse past := by
    rw [← hzero]
    exact Fin.cons_self_tail (linearMarkovFinitePathReverse past)
  rw [hcons]
  exact linearMarkovFinitePathReverse_involutive (Ω := Ω) (n + 1) past

/-- Packing after chronological splitting is exact. -/
@[simp] theorem linearMarkovCenteredFinitePathToChronologicalSum_unpack
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePathSum Ω n) :
    linearMarkovCenteredFinitePathToChronologicalSum
        (linearMarkovChronologicalSumToCenteredFinitePath path) = path := by
  let past : Fin (n + 2) → Ω :=
    fun i => path (Fin.castAdd (n + 1) i)
  let positive : Fin (n + 1) → Ω :=
    fun i => path (Fin.natAdd (n + 2) i)
  change
    Fin.append
        (linearMarkovFinitePathReverse
          (Fin.cons (past (Fin.last (n + 1)))
            (linearMarkovSingleChainReflectedPast past)))
        positive = path
  rw [linearMarkovSingleChainPastOfCenteredSplit]
  simpa [past, positive] using
    (Fin.append_castAdd_natAdd (f := path))

/-- Centered paths and chronological sum-indexed paths are equivalent. -/
def linearMarkovCenteredChronologicalSumEquiv
    (Ω : Type*) (n : ℕ) :
    LinearMarkovCenteredFinitePath Ω n ≃
      LinearMarkovChronologicalCenteredFinitePathSum Ω n where
  toFun := linearMarkovCenteredFinitePathToChronologicalSum
  invFun := linearMarkovChronologicalSumToCenteredFinitePath
  left_inv := linearMarkovChronologicalSumToCenteredFinitePath_pack
  right_inv := linearMarkovCenteredFinitePathToChronologicalSum_unpack

/-- Normalize a sum-indexed chronological tuple to the explicit length
`2 * n + 3`. -/
def linearMarkovChronologicalSumToExplicit
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePathSum Ω n) :
    LinearMarkovChronologicalCenteredFinitePath Ω n :=
  path ∘ Fin.cast (by omega)

/-- Regard an explicit `Fin (2 * n + 3)` tuple as the corresponding sum-indexed
tuple. -/
def linearMarkovChronologicalExplicitToSum
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePath Ω n) :
    LinearMarkovChronologicalCenteredFinitePathSum Ω n :=
  path ∘ Fin.cast (by omega)

@[simp] theorem linearMarkovChronologicalExplicitToSum_toExplicit
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePathSum Ω n) :
    linearMarkovChronologicalExplicitToSum
        (linearMarkovChronologicalSumToExplicit path) = path := by
  funext i
  simp [linearMarkovChronologicalExplicitToSum,
    linearMarkovChronologicalSumToExplicit]

@[simp] theorem linearMarkovChronologicalSumToExplicit_toSum
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePath Ω n) :
    linearMarkovChronologicalSumToExplicit
        (linearMarkovChronologicalExplicitToSum path) = path := by
  funext i
  simp [linearMarkovChronologicalExplicitToSum,
    linearMarkovChronologicalSumToExplicit]

/-- Pack a centered path into the explicit chronological carrier
`Fin (2 * n + 3) → Ω`. -/
def linearMarkovCenteredFinitePathToChronological
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω n) :
    LinearMarkovChronologicalCenteredFinitePath Ω n :=
  linearMarkovChronologicalSumToExplicit
    (linearMarkovCenteredFinitePathToChronologicalSum path)

/-- Unpack an explicit chronological centered tuple. -/
def linearMarkovChronologicalToCenteredFinitePath
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePath Ω n) :
    LinearMarkovCenteredFinitePath Ω n :=
  linearMarkovChronologicalSumToCenteredFinitePath
    (linearMarkovChronologicalExplicitToSum path)

@[simp] theorem linearMarkovChronologicalToCenteredFinitePath_pack
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω n) :
    linearMarkovChronologicalToCenteredFinitePath
        (linearMarkovCenteredFinitePathToChronological path) = path := by
  simp [linearMarkovChronologicalToCenteredFinitePath,
    linearMarkovCenteredFinitePathToChronological]

@[simp] theorem linearMarkovCenteredFinitePathToChronological_unpack
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovChronologicalCenteredFinitePath Ω n) :
    linearMarkovCenteredFinitePathToChronological
        (linearMarkovChronologicalToCenteredFinitePath path) = path := by
  simp [linearMarkovChronologicalToCenteredFinitePath,
    linearMarkovCenteredFinitePathToChronological]

/-- The explicit chronological carrier is equivalent to the centered carrier. -/
def linearMarkovCenteredChronologicalEquiv
    (Ω : Type*) (n : ℕ) :
    LinearMarkovCenteredFinitePath Ω n ≃
      LinearMarkovChronologicalCenteredFinitePath Ω n where
  toFun := linearMarkovCenteredFinitePathToChronological
  invFun := linearMarkovChronologicalToCenteredFinitePath
  left_inv := linearMarkovChronologicalToCenteredFinitePath_pack
  right_inv := linearMarkovCenteredFinitePathToChronological_unpack

/-- The explicit chronological PMF obtained from one finite Markov chain centered
at its terminal boundary. -/
def linearMarkovChronologicalCenteredFinitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    PMF (LinearMarkovChronologicalCenteredFinitePath Ω n) :=
  (linearMarkovSingleChainCenteredFinitePathPMF initial transition n).map
    linearMarkovCenteredFinitePathToChronological

/-- Unpacking the chronological PMF recovers the single-chain centered PMF. -/
theorem linearMarkovChronologicalCenteredFinitePathPMF_map_unpack
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovChronologicalCenteredFinitePathPMF initial transition n).map
        linearMarkovChronologicalToCenteredFinitePath =
      linearMarkovSingleChainCenteredFinitePathPMF initial transition n := by
  unfold linearMarkovChronologicalCenteredFinitePathPMF
  rw [PMF.map_comp]
  simpa [Function.comp_def] using
    PMF.map_id (linearMarkovSingleChainCenteredFinitePathPMF initial transition n)

/-- Under detailed balance, unpacking the explicit chronological law gives the
existing doubled-future centered PMF exactly. -/
theorem linearMarkovChronologicalCenteredFinitePathPMF_map_unpack_eq_centered
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovChronologicalCenteredFinitePathPMF initial transition n).map
        linearMarkovChronologicalToCenteredFinitePath =
      linearMarkovCenteredFinitePathPMF initial transition n := by
  rw [linearMarkovChronologicalCenteredFinitePathPMF_map_unpack]
  exact
    linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
      initial transition hdb n

end

end MathlibAnalytic
end MGAP4D
