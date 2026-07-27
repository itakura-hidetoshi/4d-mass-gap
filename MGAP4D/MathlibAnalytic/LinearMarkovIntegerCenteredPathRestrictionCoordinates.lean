import MGAP4D.MathlibAnalytic.LinearMarkovIntegerCenteredPathProjectiveFamily
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Embed a coordinate of the smaller symmetric interval into the centered block
of the interval whose radius is larger by `d`. -/
def linearMarkovIntegerCenteredIndexEmbed
    (n d : ℕ) (i : Fin (2 * n + 3)) :
    Fin (2 * (n + d) + 3) :=
  ⟨i.1 + d, by omega⟩

@[simp] theorem linearMarkovIntegerCenteredIndexEmbed_val
    (n d : ℕ) (i : Fin (2 * n + 3)) :
    (linearMarkovIntegerCenteredIndexEmbed n d i).1 = i.1 + d :=
  rfl

/-- Reindex a centered finite path along an equality of radii. -/
def linearMarkovIntegerCenteredFinitePathCast
    {Ω : Type*} {a b : ℕ} (h : a = b)
    (path : LinearMarkovIntegerCenteredFinitePath Ω a) :
    LinearMarkovIntegerCenteredFinitePath Ω b := by
  subst b
  exact path

@[simp] theorem linearMarkovIntegerCenteredFinitePathCast_rfl
    {Ω : Type*} {a : ℕ}
    (path : LinearMarkovIntegerCenteredFinitePath Ω a) :
    linearMarkovIntegerCenteredFinitePathCast rfl path = path :=
  rfl

/-- Centered coordinate embedding preserves the represented integer time. -/
@[simp] theorem linearMarkovIntegerCenteredTime_indexEmbed
    (n d : ℕ) (i : Fin (2 * n + 3)) :
    linearMarkovIntegerCenteredTime
        (linearMarkovIntegerCenteredIndexEmbed n d i) =
      linearMarkovIntegerCenteredTime i := by
  unfold linearMarkovIntegerCenteredTime
  simp [linearMarkovIntegerCenteredIndexEmbed]
  omega

/-- Before arithmetic normalization, packing after deleting the two terminal
future coordinates reads the central block of the original packed path. -/
theorem linearMarkovCenteredFinitePathToChronologicalSum_init_apply
    {Ω : Type*} (n : ℕ)
    (path : LinearMarkovCenteredFinitePath Ω (n + 1))
    (i : Fin ((n + 2) + (n + 1))) :
    linearMarkovCenteredFinitePathToChronologicalSum
        (linearMarkovCenteredFinitePathInit path) i =
      linearMarkovCenteredFinitePathToChronologicalSum path
        ⟨i.1 + 1, by omega⟩ := by
  rcases path with ⟨negative, boundary, positive⟩
  unfold linearMarkovCenteredFinitePathToChronologicalSum
    linearMarkovCenteredFinitePathInit
  refine Fin.addCases ?_ ?_ i
  · intro a
    rw [Fin.append_left]
    have hk :
        (⟨(Fin.castAdd (n + 1) a).1 + 1, by omega⟩ :
          Fin ((n + 3) + (n + 2))) =
          Fin.castAdd (n + 2) a.succ := by
      apply Fin.ext
      rfl
    rw [hk, Fin.append_left]
    unfold linearMarkovFinitePathReverse
    have hrev : a.succ.rev = a.rev.castSucc := by
      apply Fin.ext
      simp
    rw [hrev]
    refine Fin.cases ?_ ?_ a.rev
    · simp
    · intro j
      rfl
  · intro b
    rw [Fin.append_right]
    have hk :
        (⟨(Fin.natAdd (n + 2) b).1 + 1, by omega⟩ :
          Fin ((n + 3) + (n + 2))) =
          Fin.natAdd (n + 3) b.castSucc := by
      apply Fin.ext
      change (n + 2 + b.1) + 1 = n + 3 + b.1
      omega
    rw [hk, Fin.append_right]
    rfl

/-- One outer-coordinate cut reads the central subtuple of the original path. -/
theorem linearMarkovChronologicalCenteredFinitePathInit_apply
    {Ω : Type*} (n : ℕ)
    (path : LinearMarkovIntegerCenteredFinitePath Ω (n + 1))
    (i : Fin (2 * n + 3)) :
    linearMarkovChronologicalCenteredFinitePathInit path i =
      path (linearMarkovIntegerCenteredIndexEmbed n 1 i) := by
  let centered := linearMarkovChronologicalToCenteredFinitePath path
  have hpath :
      linearMarkovCenteredFinitePathToChronological centered = path :=
    linearMarkovCenteredFinitePathToChronological_unpack path
  rw [← hpath]
  rw [linearMarkovChronologicalCenteredFinitePathInit_pack]
  unfold linearMarkovCenteredFinitePathToChronological
    linearMarkovChronologicalSumToExplicit
  exact linearMarkovCenteredFinitePathToChronologicalSum_init_apply
    n centered (Fin.cast (by omega) i)

/-- Iterated outer-coordinate restriction is exactly central-block coordinate
restriction `i ↦ i + d`. -/
theorem linearMarkovIntegerCenteredFinitePathRestrictBy_apply
    {Ω : Type*} (n d : ℕ)
    (path : LinearMarkovIntegerCenteredFinitePath Ω (n + d))
    (i : Fin (2 * n + 3)) :
    linearMarkovIntegerCenteredFinitePathRestrictBy n d path i =
      path (linearMarkovIntegerCenteredIndexEmbed n d i) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change
        linearMarkovIntegerCenteredFinitePathRestrictBy n d
            (linearMarkovChronologicalCenteredFinitePathInit path) i =
          path (linearMarkovIntegerCenteredIndexEmbed n (d + 1) i)
      rw [ih]
      rw [linearMarkovChronologicalCenteredFinitePathInit_apply (n + d)]
      apply congrArg path
      apply Fin.ext
      rfl

end

end MathlibAnalytic
end MGAP4D
