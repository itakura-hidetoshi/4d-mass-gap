import MGAP4D.MathlibAnalytic.LinearMarkovIntegerCenteredPathRestrictionCoordinates
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A canonical radius containing every integer time in a finite set. -/
def linearMarkovIntegerFiniteSetRadius (J : Finset ℤ) : ℕ :=
  J.sup Int.natAbs

/-- Every member of a finite integer set lies within its canonical radius. -/
theorem linearMarkovIntegerFiniteSet_natAbs_le_radius
    (J : Finset ℤ) {t : ℤ} (ht : t ∈ J) :
    t.natAbs ≤ linearMarkovIntegerFiniteSetRadius J := by
  unfold linearMarkovIntegerFiniteSetRadius
  exact Finset.le_sup (f := Int.natAbs) ht

/-- An integer bounded in absolute value lies between the corresponding signed
bounds. -/
theorem int_bounds_of_natAbs_le
    (t : ℤ) (r : ℕ) (h : t.natAbs ≤ r) :
    -((r : ℕ) : ℤ) ≤ t ∧ t ≤ ((r : ℕ) : ℤ) := by
  rcases t with n | n <;> simp at h ⊢ <;> omega

/-- Coordinate in the symmetric interval of horizon `r` representing a bounded
integer time. -/
def linearMarkovIntegerCenteredIndexOfBound
    (r : ℕ) (t : ℤ) (h : t.natAbs ≤ r) :
    Fin (2 * r + 3) := by
  have hb := int_bounds_of_natAbs_le t r h
  refine ⟨Int.toNat (t + ((r + 1 : ℕ) : ℤ)), ?_⟩
  omega

/-- The bounded-time coordinate represents exactly the requested integer time. -/
@[simp] theorem linearMarkovIntegerCenteredTime_indexOfBound
    (r : ℕ) (t : ℤ) (h : t.natAbs ≤ r) :
    linearMarkovIntegerCenteredTime
        (linearMarkovIntegerCenteredIndexOfBound r t h) = t := by
  have hb := int_bounds_of_natAbs_le t r h
  have hnonneg : 0 ≤ t + ((r + 1 : ℕ) : ℤ) := by omega
  unfold linearMarkovIntegerCenteredIndexOfBound
    linearMarkovIntegerCenteredTime
  simp [Int.toNat_of_nonneg hnonneg]
  omega

/-- Coordinate of a member of `J` in the canonical symmetric interval for `J`. -/
def linearMarkovIntegerFiniteSetIndex
    (J : Finset ℤ) (t : J) :
    Fin (2 * linearMarkovIntegerFiniteSetRadius J + 3) :=
  linearMarkovIntegerCenteredIndexOfBound
    (linearMarkovIntegerFiniteSetRadius J) t.1
    (linearMarkovIntegerFiniteSet_natAbs_le_radius J t.2)

@[simp] theorem linearMarkovIntegerCenteredTime_finiteSetIndex
    (J : Finset ℤ) (t : J) :
    linearMarkovIntegerCenteredTime
        (linearMarkovIntegerFiniteSetIndex J t) = t.1 := by
  exact linearMarkovIntegerCenteredTime_indexOfBound _ _ _

/-- Observe a finite set of integer times in its canonical symmetric path. -/
def linearMarkovIntegerFiniteSetObserve
    {Ω : Type*} (J : Finset ℤ) :
    LinearMarkovIntegerCenteredFinitePath Ω
        (linearMarkovIntegerFiniteSetRadius J) →
      (∀ t : J, Ω) :=
  fun path t => path (linearMarkovIntegerFiniteSetIndex J t)

/-- Canonical radius is monotone under inclusion of finite time sets. -/
theorem linearMarkovIntegerFiniteSetRadius_mono
    {J I : Finset ℤ} (hJI : J ⊆ I) :
    linearMarkovIntegerFiniteSetRadius J ≤
      linearMarkovIntegerFiniteSetRadius I := by
  unfold linearMarkovIntegerFiniteSetRadius
  apply Finset.sup_le
  intro t ht
  exact Finset.le_sup (f := Int.natAbs) (hJI ht)

/-- The coordinate selected for a time in `J` embeds into any larger canonical
interval at the same integer time. -/
theorem linearMarkovIntegerFiniteSetIndex_embed
    {J I : Finset ℤ} (hJI : J ⊆ I) (t : J) :
    linearMarkovIntegerCenteredIndexEmbed
        (linearMarkovIntegerFiniteSetRadius J)
        (linearMarkovIntegerFiniteSetRadius I -
          linearMarkovIntegerFiniteSetRadius J)
        (linearMarkovIntegerFiniteSetIndex J t) =
      linearMarkovIntegerFiniteSetIndex I ⟨t.1, hJI t.2⟩ := by
  apply linearMarkovIntegerCenteredTime_injective
    (linearMarkovIntegerFiniteSetRadius I)
  rw [linearMarkovIntegerCenteredTime_indexEmbed]
  simp

/-- Observing `J` after restricting the canonical `I`-interval agrees pointwise
with restricting the `I`-observation to `J`. -/
theorem linearMarkovIntegerFiniteSetObserve_restrict
    {Ω : Type*} {J I : Finset ℤ} (hJI : J ⊆ I)
    (path : LinearMarkovIntegerCenteredFinitePath Ω
      (linearMarkovIntegerFiniteSetRadius J +
        (linearMarkovIntegerFiniteSetRadius I -
          linearMarkovIntegerFiniteSetRadius J))) :
    linearMarkovIntegerFiniteSetObserve J
        (linearMarkovIntegerCenteredFinitePathRestrictBy
          (linearMarkovIntegerFiniteSetRadius J)
          (linearMarkovIntegerFiniteSetRadius I -
            linearMarkovIntegerFiniteSetRadius J) path) =
      Finset.restrict₂ hJI
        (linearMarkovIntegerFiniteSetObserve I
          (linearMarkovIntegerCenteredFinitePathCast
            (Nat.add_sub_of_le
              (linearMarkovIntegerFiniteSetRadius_mono hJI)) path)) := by
  funext t
  rw [linearMarkovIntegerCenteredFinitePathRestrictBy_apply]
  unfold linearMarkovIntegerFiniteSetObserve
  rw [linearMarkovIntegerFiniteSetIndex_embed hJI]
  rfl

/-- The finite-dimensional law on an arbitrary finite set of integer times. -/
def linearMarkovIntegerFiniteMarginalPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (J : Finset ℤ) : PMF (∀ t : J, Ω) :=
  (linearMarkovIntegerCenteredFinitePathPMF initial transition
    (linearMarkovIntegerFiniteSetRadius J)).map
      (linearMarkovIntegerFiniteSetObserve J)

/-- Arbitrary finite integer-time marginals are projectively compatible. -/
theorem linearMarkovIntegerFiniteMarginalPMF_projective
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    ∀ (I J : Finset ℤ) (hJI : J ⊆ I),
      linearMarkovIntegerFiniteMarginalPMF initial transition J =
        (linearMarkovIntegerFiniteMarginalPMF initial transition I).map
          (Finset.restrict₂ hJI) := by
  intro I J hJI
  let rJ := linearMarkovIntegerFiniteSetRadius J
  let rI := linearMarkovIntegerFiniteSetRadius I
  let d := rI - rJ
  have hr : rJ ≤ rI := linearMarkovIntegerFiniteSetRadius_mono hJI
  have hrd : rJ + d = rI := Nat.add_sub_of_le hr
  unfold linearMarkovIntegerFiniteMarginalPMF
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
    initial transition hdb rJ d]
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg
    (fun f =>
      (linearMarkovIntegerCenteredFinitePathPMF initial transition (rJ + d)).map f)
  funext path
  have hobs := linearMarkovIntegerFiniteSetObserve_restrict
    (Ω := Ω) hJI path
  simpa [rJ, rI, d, hrd] using hobs

end

end MathlibAnalytic
end MGAP4D
