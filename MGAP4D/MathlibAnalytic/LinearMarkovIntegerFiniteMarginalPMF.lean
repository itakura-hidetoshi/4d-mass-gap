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
  simp
  omega

/-- Coordinate of a member of `J` in any symmetric interval whose radius contains
`J`. -/
def linearMarkovIntegerFiniteSetIndexAt
    (J : Finset ℤ) (r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r)
    (t : J) : Fin (2 * r + 3) :=
  linearMarkovIntegerCenteredIndexOfBound r t.1
    ((linearMarkovIntegerFiniteSet_natAbs_le_radius J t.2).trans hJ)

@[simp] theorem linearMarkovIntegerCenteredTime_finiteSetIndexAt
    (J : Finset ℤ) (r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r)
    (t : J) :
    linearMarkovIntegerCenteredTime
        (linearMarkovIntegerFiniteSetIndexAt J r hJ t) = t.1 := by
  exact linearMarkovIntegerCenteredTime_indexOfBound _ _ _

/-- Coordinate of a member of `J` in its canonical symmetric interval. -/
def linearMarkovIntegerFiniteSetIndex
    (J : Finset ℤ) (t : J) :
    Fin (2 * linearMarkovIntegerFiniteSetRadius J + 3) :=
  linearMarkovIntegerFiniteSetIndexAt J
    (linearMarkovIntegerFiniteSetRadius J) le_rfl t

@[simp] theorem linearMarkovIntegerCenteredTime_finiteSetIndex
    (J : Finset ℤ) (t : J) :
    linearMarkovIntegerCenteredTime
        (linearMarkovIntegerFiniteSetIndex J t) = t.1 := by
  exact linearMarkovIntegerCenteredTime_finiteSetIndexAt _ _ _ _

/-- Observe a finite set of integer times in any containing symmetric interval. -/
def linearMarkovIntegerFiniteSetObserveAt
    {Ω : Type*} (J : Finset ℤ) (r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r) :
    LinearMarkovIntegerCenteredFinitePath Ω r → (∀ t : J, Ω) :=
  fun path t => path (linearMarkovIntegerFiniteSetIndexAt J r hJ t)

/-- Observe a finite set of integer times in its canonical symmetric interval. -/
def linearMarkovIntegerFiniteSetObserve
    {Ω : Type*} (J : Finset ℤ) :
    LinearMarkovIntegerCenteredFinitePath Ω
        (linearMarkovIntegerFiniteSetRadius J) → (∀ t : J, Ω) :=
  linearMarkovIntegerFiniteSetObserveAt J
    (linearMarkovIntegerFiniteSetRadius J) le_rfl

/-- Coordinate restriction between finite constant products. -/
def linearMarkovIntegerFiniteSetRestrict
    {Ω : Type*} {I J : Finset ℤ} (hJI : J ⊆ I) :
    (∀ t : I, Ω) → (∀ t : J, Ω) :=
  fun values t => values ⟨t.1, hJI t.2⟩

/-- The explicit constant-product restriction is the standard dependent-product
restriction. -/
theorem linearMarkovIntegerFiniteSetRestrict_eq_finsetRestrict
    {Ω : Type*} {I J : Finset ℤ} (hJI : J ⊆ I) :
    (linearMarkovIntegerFiniteSetRestrict hJI :
      (∀ t : I, Ω) → (∀ t : J, Ω)) =
      Finset.restrict₂ hJI := by
  rfl

/-- Canonical radius is monotone under inclusion of finite time sets. -/
theorem linearMarkovIntegerFiniteSetRadius_mono
    {J I : Finset ℤ} (hJI : J ⊆ I) :
    linearMarkovIntegerFiniteSetRadius J ≤
      linearMarkovIntegerFiniteSetRadius I := by
  unfold linearMarkovIntegerFiniteSetRadius
  apply Finset.sup_le
  intro t ht
  exact Finset.le_sup (f := Int.natAbs) (hJI ht)

/-- Restricting a containing symmetric path to the canonical `J`-interval and
then observing `J` agrees with observing `I` in the same containing interval and
forgetting the coordinates outside `J`. -/
theorem linearMarkovIntegerFiniteSetObserve_restrictBy
    {Ω : Type*} {J I : Finset ℤ} (hJI : J ⊆ I)
    (d : ℕ)
    (hI : linearMarkovIntegerFiniteSetRadius I ≤
      linearMarkovIntegerFiniteSetRadius J + d)
    (path : LinearMarkovIntegerCenteredFinitePath Ω
      (linearMarkovIntegerFiniteSetRadius J + d)) :
    linearMarkovIntegerFiniteSetObserve J
        (linearMarkovIntegerCenteredFinitePathRestrictBy
          (linearMarkovIntegerFiniteSetRadius J) d path) =
      linearMarkovIntegerFiniteSetRestrict hJI
        (linearMarkovIntegerFiniteSetObserveAt I
          (linearMarkovIntegerFiniteSetRadius J + d) hI path) := by
  funext t
  rw [linearMarkovIntegerCenteredFinitePathRestrictBy_apply]
  unfold linearMarkovIntegerFiniteSetObserve
    linearMarkovIntegerFiniteSetObserveAt
    linearMarkovIntegerFiniteSetRestrict
  apply congrArg path
  apply linearMarkovIntegerCenteredTime_injective
    (linearMarkovIntegerFiniteSetRadius J + d)
  rw [linearMarkovIntegerCenteredTime_indexEmbed]
  simp

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
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (I J : Finset ℤ) (hJI : J ⊆ I) :
    linearMarkovIntegerFiniteMarginalPMF initial transition J =
      (linearMarkovIntegerFiniteMarginalPMF initial transition I).map
        (Finset.restrict₂ hJI :
          (∀ t : I, Ω) → (∀ t : J, Ω)) := by
  let rJ := linearMarkovIntegerFiniteSetRadius J
  let rI := linearMarkovIntegerFiniteSetRadius I
  let d := rI - rJ
  have hr : rJ ≤ rI := linearMarkovIntegerFiniteSetRadius_mono hJI
  have hrd : rJ + d = rI := Nat.add_sub_of_le hr
  have hI : linearMarkovIntegerFiniteSetRadius I ≤
      linearMarkovIntegerFiniteSetRadius J + d := by
    simpa [rJ, rI] using hrd.symm.le
  unfold linearMarkovIntegerFiniteMarginalPMF
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
    initial transition hdb rJ d]
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg
    (fun f =>
      (linearMarkovIntegerCenteredFinitePathPMF initial transition (rJ + d)).map f)
  funext path
  have hobs := linearMarkovIntegerFiniteSetObserve_restrictBy
    (Ω := Ω) hJI d hI path
  rw [linearMarkovIntegerFiniteSetRestrict_eq_finsetRestrict] at hobs
  simpa [rJ, rI, hrd] using hobs

end

end MathlibAnalytic
end MGAP4D
