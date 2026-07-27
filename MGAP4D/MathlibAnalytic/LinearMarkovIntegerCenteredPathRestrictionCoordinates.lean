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

/-- One outer-coordinate cut reads the central subtuple of the original path. -/
theorem linearMarkovChronologicalCenteredFinitePathInit_apply
    {Ω : Type*} (n : ℕ)
    (path : LinearMarkovIntegerCenteredFinitePath Ω (n + 1))
    (i : Fin (2 * n + 3)) :
    linearMarkovChronologicalCenteredFinitePathInit path i =
      path (linearMarkovIntegerCenteredIndexEmbed n 1 i) := by
  rw [← linearMarkovCenteredFinitePathToChronological_unpack path]
  rw [linearMarkovChronologicalCenteredFinitePathInit_pack]
  let centered := linearMarkovChronologicalToCenteredFinitePath path
  rcases centered with ⟨negative, boundary, positive⟩
  unfold linearMarkovCenteredFinitePathToChronological
    linearMarkovChronologicalSumToExplicit
    linearMarkovCenteredFinitePathToChronologicalSum
    linearMarkovCenteredFinitePathInit
    linearMarkovIntegerCenteredIndexEmbed
  simp [linearMarkovFinitePathReverse, Function.comp_def]
  split <;> omega

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
      congr 1
      apply Fin.ext
      simp [linearMarkovIntegerCenteredIndexEmbed]
      omega

end

end MathlibAnalytic
end MGAP4D
