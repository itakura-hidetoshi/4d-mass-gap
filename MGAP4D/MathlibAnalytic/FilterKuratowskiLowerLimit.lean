import MGAP4D.MathlibAnalytic.FilterKuratowskiOuterLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

universe u v

namespace FilterSet

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- The Painlevé–Kuratowski lower limit of a set-valued map along a filter.
A point belongs to the lower limit when every neighborhood meets every
sufficiently late member of the family. -/
def kuratowskiLowerLimit (l : Filter ι) (s : ι → Set X) : Set X :=
  {x | ∀ U ∈ nhds x, ∀ᶠ i in l, (U ∩ s i).Nonempty}

/-- Lower-limit points witnessed by one selection that is eventually admissible
and converges to the candidate point. -/
def convergentSelectionLowerLimit (l : Filter ι) (s : ι → Set X) : Set X :=
  {x | ∃ f : ι → X, Tendsto f l (nhds x) ∧ ∀ᶠ i in l, f i ∈ s i}

@[simp]
theorem mem_kuratowskiLowerLimit {l : Filter ι} {s : ι → Set X} {x : X} :
    x ∈ kuratowskiLowerLimit l s ↔
      ∀ U ∈ nhds x, ∀ᶠ i in l, (U ∩ s i).Nonempty :=
  Iff.rfl

@[simp]
theorem mem_convergentSelectionLowerLimit
    {l : Filter ι} {s : ι → Set X} {x : X} :
    x ∈ convergentSelectionLowerLimit l s ↔
      ∃ f : ι → X, Tendsto f l (nhds x) ∧ ∀ᶠ i in l, f i ∈ s i :=
  Iff.rfl

/-- A convergent eventually admissible selection is a recovery selection and
therefore determines a Painlevé–Kuratowski lower-limit point. -/
theorem convergentSelectionLowerLimit_subset_kuratowskiLowerLimit
    (l : Filter ι) (s : ι → Set X) :
    convergentSelectionLowerLimit l s ⊆ kuratowskiLowerLimit l s := by
  rintro x ⟨f, hf, hMem⟩ U hU
  have hNear : ∀ᶠ i in l, f i ∈ U := hf.eventually hU
  filter_upwards [hNear, hMem] with i hiU hiS
  exact ⟨f i, hiU, hiS⟩

/-- For a nontrivial indexing filter, every lower-limit point is also an
outer-limit point. -/
theorem kuratowskiLowerLimit_subset_kuratowskiOuterLimit
    (l : Filter ι) [NeBot l] (s : ι → Set X) :
    kuratowskiLowerLimit l s ⊆ kuratowskiOuterLimit l s := by
  intro x hx A hA
  rw [mem_closure_iff_nhds]
  intro U hU
  have hMeet : ∀ᶠ i in l, (U ∩ s i).Nonempty := hx U hU
  have hTail : ∀ᶠ i in l, i ∈ A := hA
  rcases (hMeet.and hTail).exists with ⟨i, hiMeet, hiA⟩
  rcases hiMeet with ⟨y, hyU, hyS⟩
  exact ⟨y, hyU,
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hyS⟩⟩⟩

/-- A recovery selection also witnesses membership in the outer limit whenever
the indexing filter is nontrivial. -/
theorem convergentSelectionLowerLimit_subset_kuratowskiOuterLimit
    (l : Filter ι) [NeBot l] (s : ι → Set X) :
    convergentSelectionLowerLimit l s ⊆ kuratowskiOuterLimit l s :=
  Set.Subset.trans
    (convergentSelectionLowerLimit_subset_kuratowskiLowerLimit l s)
    (kuratowskiLowerLimit_subset_kuratowskiOuterLimit l s)

/-- Singleton outer containment together with one lower-limit recovery point
identifies both Painlevé–Kuratowski limits with the same singleton. -/
theorem kuratowskiLimits_eq_singleton_of_outer_subset_of_mem_lower
    (l : Filter ι) [NeBot l] (s : ι → Set X) (x : X)
    (hOuter : kuratowskiOuterLimit l s ⊆ {x})
    (hLower : x ∈ kuratowskiLowerLimit l s) :
    kuratowskiOuterLimit l s = {x} ∧ kuratowskiLowerLimit l s = {x} := by
  have hxOuter : x ∈ kuratowskiOuterLimit l s :=
    kuratowskiLowerLimit_subset_kuratowskiOuterLimit l s hLower
  constructor
  · exact Set.Subset.antisymm hOuter (by
      intro y hy
      have hyx : y = x := by simpa only [Set.mem_singleton_iff] using hy
      simpa only [hyx] using hxOuter)
  · apply Set.Subset.antisymm
    · exact Set.Subset.trans
        (kuratowskiLowerLimit_subset_kuratowskiOuterLimit l s) hOuter
    · intro y hy
      have hyx : y = x := by simpa only [Set.mem_singleton_iff] using hy
      simpa only [hyx] using hLower

end FilterSet

end MathlibAnalytic
end MGAP4D
