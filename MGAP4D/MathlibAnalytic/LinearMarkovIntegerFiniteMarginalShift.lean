import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathEndpointRestriction
import MGAP4D.MathlibAnalytic.LinearMarkovIntegerFiniteMarginalPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Translate a finite set of integer times by a nonnegative displacement. -/
def linearMarkovIntegerFiniteSetNatShift
    (J : Finset ℤ) (d : ℕ) : Finset ℤ :=
  J.image fun t => t + ((d : ℕ) : ℤ)

@[simp] theorem linearMarkovIntegerFiniteSet_mem_natShift
    (J : Finset ℤ) (d : ℕ) (t : J) :
    t.1 + ((d : ℕ) : ℤ) ∈ linearMarkovIntegerFiniteSetNatShift J d := by
  exact Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩

/-- Reindex values on the translated time set back to the original finite set. -/
def linearMarkovIntegerFiniteSetNatShiftReindex
    {Ω : Type*} (J : Finset ℤ) (d : ℕ) :
    (∀ _s : linearMarkovIntegerFiniteSetNatShift J d, Ω) →
      (∀ _t : J, Ω) :=
  fun values t =>
    values ⟨t.1 + ((d : ℕ) : ℤ),
      linearMarkovIntegerFiniteSet_mem_natShift J d t⟩

/-- Every arbitrary finite marginal can be computed inside any larger symmetric
integer interval. -/
theorem linearMarkovIntegerCenteredFinitePathPMF_map_observeAt
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) (r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r) :
    (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetObserveAt J r hJ) =
      linearMarkovIntegerFiniteMarginalPMF initial transition J := by
  let rJ := linearMarkovIntegerFiniteSetRadius J
  let d := r - rJ
  have hr : rJ ≤ r := hJ
  have hrd : rJ + d = r := Nat.add_sub_of_le hr
  cases hrd
  unfold linearMarkovIntegerFiniteMarginalPMF
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
    initial transition hdb rJ d]
  rw [PMF.map_comp]
  apply congrArg
    (fun f =>
      (linearMarkovIntegerCenteredFinitePathPMF initial transition (rJ + d)).map f)
  funext path
  have hobs := linearMarkovIntegerFiniteSetObserve_restrictBy
    (Ω := Ω) (J := J) (I := J) (fun _ ht => ht) d
    (show linearMarkovIntegerFiniteSetRadius J ≤ rJ + d by
      simpa [rJ] using Nat.le_add_right rJ d)
    path
  simpa [rJ, linearMarkovIntegerFiniteSetRestrict] using hobs.symm

/-- In a common centered interval, the coordinate representing `t + d` is the
coordinate representing `t`, shifted forward by exactly `d` positions. -/
theorem linearMarkovIntegerCenteredIndexOfBound_natShift
    (r d : ℕ) (t : ℤ)
    (ht : t.natAbs ≤ r)
    (htd : (t + ((d : ℕ) : ℤ)).natAbs ≤ r) :
    linearMarkovIntegerCenteredIndexOfBound r
        (t + ((d : ℕ) : ℤ)) htd =
      ⟨(linearMarkovIntegerCenteredIndexOfBound r t ht).1 + d,
        by
          have hupper := (int_bounds_of_natAbs_le
            (t + ((d : ℕ) : ℤ)) r htd).2
          unfold linearMarkovIntegerCenteredIndexOfBound
          simp
          omega⟩ := by
  apply Fin.ext
  have htBounds := int_bounds_of_natAbs_le t r ht
  have htdBounds := int_bounds_of_natAbs_le
    (t + ((d : ℕ) : ℤ)) r htd
  unfold linearMarkovIntegerCenteredIndexOfBound
  simp
  omega

/-- Observe the original index set after translating every requested time by
`d`, while using one common centered interval. -/
def linearMarkovIntegerFiniteSetNatShiftObserveAt
    {Ω : Type*} (J : Finset ℤ) (d r : ℕ)
    (hShift : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerFiniteSetNatShift J d) ≤ r) :
    LinearMarkovIntegerCenteredFinitePath Ω r → (∀ _t : J, Ω) :=
  fun path =>
    linearMarkovIntegerFiniteSetNatShiftReindex J d
      (linearMarkovIntegerFiniteSetObserveAt
        (linearMarkovIntegerFiniteSetNatShift J d) r hShift path)

/-- The shifted finite-set observation is evaluation at the coordinate whose
integer time is `t + d`. -/
theorem linearMarkovIntegerFiniteSetNatShiftObserveAt_apply
    {Ω : Type*} (J : Finset ℤ) (d r : ℕ)
    (hShift : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerFiniteSetNatShift J d) ≤ r)
    (path : LinearMarkovIntegerCenteredFinitePath Ω r) (t : J) :
    linearMarkovIntegerFiniteSetNatShiftObserveAt J d r hShift path t =
      path (linearMarkovIntegerCenteredIndexOfBound r
        (t.1 + ((d : ℕ) : ℤ))
        ((linearMarkovIntegerFiniteSet_natAbs_le_radius
          (linearMarkovIntegerFiniteSetNatShift J d)
          (linearMarkovIntegerFiniteSet_mem_natShift J d t)).trans hShift)) := by
  rfl

/-- Stationarity of the finite Markov path makes every common-radius finite
observation invariant under a nonnegative integer-time translation. -/
theorem linearMarkovIntegerCenteredFinitePathPMF_map_natShiftObserveAt
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) (d r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r)
    (hShift : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerFiniteSetNatShift J d) ≤ r) :
    (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetNatShiftObserveAt J d r hShift) =
      (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetObserveAt J r hJ) := by
  let n := 2 * r + 2
  have hbase :
      linearMarkovIntegerCenteredFinitePathPMF initial transition r =
        linearMarkovFinitePathPMF initial transition n := by
    exact linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
      initial transition r
  rw [hbase]
  let big := linearMarkovFinitePathPMF initial transition (n + d)
  calc
    (linearMarkovFinitePathPMF initial transition n).map
        (linearMarkovIntegerFiniteSetNatShiftObserveAt J d r hShift) =
      (big.map (linearMarkovFinitePathInitBy n d)).map
        (linearMarkovIntegerFiniteSetNatShiftObserveAt J d r hShift) := by
          rw [linearMarkovFinitePathPMF_map_initBy]
    _ = big.map
        (linearMarkovIntegerFiniteSetNatShiftObserveAt J d r hShift ∘
          linearMarkovFinitePathInitBy n d) := by
          rw [PMF.map_comp]
    _ = big.map
        (linearMarkovIntegerFiniteSetObserveAt J r hJ ∘
          linearMarkovFinitePathTailBy n d) := by
          apply congrArg (fun f => big.map f)
          funext path t
          rw [Function.comp_apply, Function.comp_apply]
          rw [linearMarkovIntegerFiniteSetNatShiftObserveAt_apply]
          unfold linearMarkovIntegerFiniteSetObserveAt
            linearMarkovFinitePathInitBy linearMarkovFinitePathTailBy
          apply congrArg path
          apply Fin.ext
          have ht : t.1.natAbs ≤ r :=
            (linearMarkovIntegerFiniteSet_natAbs_le_radius J t.2).trans hJ
          have htd : (t.1 + ((d : ℕ) : ℤ)).natAbs ≤ r :=
            (linearMarkovIntegerFiniteSet_natAbs_le_radius
              (linearMarkovIntegerFiniteSetNatShift J d)
              (linearMarkovIntegerFiniteSet_mem_natShift J d t)).trans hShift
          have hindex := linearMarkovIntegerCenteredIndexOfBound_natShift
            r d t.1 ht htd
          exact congrArg Fin.val hindex
    _ = (big.map (linearMarkovFinitePathTailBy n d)).map
        (linearMarkovIntegerFiniteSetObserveAt J r hJ) := by
          rw [PMF.map_comp]
    _ = (linearMarkovFinitePathPMF initial transition n).map
        (linearMarkovIntegerFiniteSetObserveAt J r hJ) := by
          rw [linearMarkovFinitePathPMF_map_tailBy_of_detailedBalanceReal
            initial transition hdb n d]

/-- Every arbitrary finite integer-time marginal is invariant under a
nonnegative translation, after canonical coordinate reindexing. -/
theorem linearMarkovIntegerFiniteMarginalPMF_map_natShiftReindex
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) (d : ℕ) :
    (linearMarkovIntegerFiniteMarginalPMF initial transition
        (linearMarkovIntegerFiniteSetNatShift J d)).map
      (linearMarkovIntegerFiniteSetNatShiftReindex J d) =
    linearMarkovIntegerFiniteMarginalPMF initial transition J := by
  let K := linearMarkovIntegerFiniteSetNatShift J d
  let r := max (linearMarkovIntegerFiniteSetRadius J)
    (linearMarkovIntegerFiniteSetRadius K)
  have hJ : linearMarkovIntegerFiniteSetRadius J ≤ r :=
    le_max_left _ _
  have hK : linearMarkovIntegerFiniteSetRadius K ≤ r :=
    le_max_right _ _
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_observeAt
    initial transition hdb K r hK]
  rw [PMF.map_comp]
  change
    (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetNatShiftObserveAt J d r hK) =
      linearMarkovIntegerFiniteMarginalPMF initial transition J
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_observeAt
    initial transition hdb J r hJ]
  exact linearMarkovIntegerCenteredFinitePathPMF_map_natShiftObserveAt
    initial transition hdb J d r hJ hK

end

end MathlibAnalytic
end MGAP4D
