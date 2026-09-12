import MGAP4D.MathlibAnalytic.FilterKuratowskiOuterLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

universe u v

namespace FilterSet

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- The filter Painlevé–Kuratowski inner limit: every neighborhood of the point
meets every sufficiently late member of the set family. -/
def kuratowskiInnerLimit (l : Filter ι) (s : ι → Set X) : Set X :=
  {x | ∀ U ∈ nhds x, ∀ᶠ i in l, ∃ y, y ∈ s i ∧ y ∈ U}

@[simp]
theorem mem_kuratowskiInnerLimit {l : Filter ι} {s : ι → Set X} {x : X} :
    x ∈ kuratowskiInnerLimit l s ↔
      ∀ U ∈ nhds x, ∀ᶠ i in l, ∃ y, y ∈ s i ∧ y ∈ U :=
  Iff.rfl

/-- A convergent eventually admissible selection gives inner-limit membership. -/
theorem mem_kuratowskiInnerLimit_of_tendsto_of_eventually_mem
    {l : Filter ι} {s : ι → Set X} {f : ι → X} {x : X}
    (hf : Tendsto f l (nhds x)) (hmem : ∀ᶠ i in l, f i ∈ s i) :
    x ∈ kuratowskiInnerLimit l s := by
  intro U hU
  filter_upwards [hf.eventually_mem hU, hmem] with i hiU his
  exact ⟨f i, his, hiU⟩

/-- For a nontrivial index filter, the Kuratowski inner limit is contained in
its tail-closure outer limit. -/
theorem kuratowskiInnerLimit_subset_kuratowskiOuterLimit
    (l : Filter ι) [NeBot l] (s : ι → Set X) :
    kuratowskiInnerLimit l s ⊆ kuratowskiOuterLimit l s := by
  intro x hx A hA
  rw [mem_closure_iff_nhds]
  intro U hU
  rcases ((show ∀ᶠ i in l, i ∈ A from hA).and (hx U hU)).exists with
    ⟨i, hiA, y, hys, hyU⟩
  exact ⟨y, hyU,
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hys⟩⟩⟩

end FilterSet

end MathlibAnalytic
end MGAP4D
