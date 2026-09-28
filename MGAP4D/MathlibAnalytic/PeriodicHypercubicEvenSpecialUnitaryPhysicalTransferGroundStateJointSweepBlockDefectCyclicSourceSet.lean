import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSecondVisitRepresentative
import Mathlib.Tactic

/-!
# Exact source set between two visits to one target link

For a canonical fixed-color sweep split as

  canonicalList = pre ++ e :: suffix,

PR #4894 shows that the operators acting between the first and second visits
to `e` occur in the cyclic order `suffix ++ pre`.

This file records the exact finite geometry of that cyclic list.  Assuming the
preserved freshness witness `e ∉ pre`, nodup of `Finset.univ.toList` implies
that `e` is also absent from `suffix`.  Consequently

  d ∈ suffix ++ pre  <->  d != e

for every link in the fixed-color fiber, and hence

  (suffix ++ pre).toFinset = Finset.univ.erase e.

Thus every cyclic between-visits source is automatically off-diagonal from the
target, while remaining in the same spatial-color fiber by construction.

No cardinality estimate, reordering of the list, response symmetry, or
positive-beta commutativity is introduced.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance cyclicSourceSetSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- In a canonical split, the cyclic between-visits list contains exactly the
fixed-color links other than the distinguished target. -/
theorem
    periodicHypercubicEvenFixedSpatialColorLink_mem_cyclicBetweenVisits_iff_ne
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e d : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix)
    (hFresh : e ∉ pre) :
    d ∈ suffix ++ pre ↔ d ≠ e := by
  classical
  have hNodup : (pre ++ e :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hTailNodup : (e :: suffix).Nodup :=
    hNodup.of_append_right
  have hSuffix : e ∉ suffix :=
    (List.nodup_cons.mp hTailNodup).1
  constructor
  · intro hd hde
    subst d
    have hd' : e ∈ suffix ∨ e ∈ pre := by
      simpa only [List.mem_append] using hd
    rcases hd' with hs | hp
    · exact hSuffix hs
    · exact hFresh hp
  · intro hne
    have hAll : d ∈ pre ++ e :: suffix := by
      rw [← hSplit]
      simp
    have hCases : d ∈ pre ∨ d = e ∨ d ∈ suffix := by
      simpa only [List.mem_append, List.mem_cons] using hAll
    rcases hCases with hp | heq | hs
    · simp only [List.mem_append]
      exact Or.inr hp
    · exact (hne heq).elim
    · simp only [List.mem_append]
      exact Or.inl hs

/-- Finset form: forgetting cyclic order leaves exactly the fixed-color source
set with the target erased. -/
theorem
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_toFinset_eq_erase
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix)
    (hFresh : e ∉ pre) :
    (suffix ++ pre).toFinset =
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).erase e := by
  classical
  ext d
  constructor
  · intro hd
    have hdList : d ∈ suffix ++ pre := by
      simpa using hd
    have hne :=
      (periodicHypercubicEvenFixedSpatialColorLink_mem_cyclicBetweenVisits_iff_ne
        H color pre suffix e d hSplit hFresh).1 hdList
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ d⟩
  · intro hd
    have hne : d ≠ e :=
      (Finset.mem_erase.mp hd).1
    have hdList : d ∈ suffix ++ pre :=
      (periodicHypercubicEvenFixedSpatialColorLink_mem_cyclicBetweenVisits_iff_ne
        H color pre suffix e d hSplit hFresh).2 hne
    simpa using hdList

/-- Every cyclic between-visits source is genuinely off-diagonal from the
target after forgetting the fixed-color subtype. -/
theorem
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix)
    (hFresh : e ∉ pre)
    (hsource : source ∈ suffix ++ pre) :
    source.1 ≠ e.1 := by
  intro hval
  have hsub : source = e :=
    Subtype.ext hval
  have hne :=
    (periodicHypercubicEvenFixedSpatialColorLink_mem_cyclicBetweenVisits_iff_ne
      H color pre suffix e source hSplit hFresh).1 hsource
  exact hne hsub

end

end MGAP4D.MathlibAnalytic
