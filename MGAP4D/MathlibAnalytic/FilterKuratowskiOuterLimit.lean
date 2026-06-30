import Mathlib.Topology.ClusterPt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

universe u v

namespace Filter

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- The Painlevé–Kuratowski outer limit of a set-valued map along a filter,
written as the intersection of the closures of all filter tails. -/
def kuratowskiOuterLimit (l : Filter ι) (s : ι → Set X) : Set X :=
  {x | ∀ A ∈ l, x ∈ closure (⋃ i ∈ A, s i)}

/-- The selection form of an outer limit: cluster points of maps that eventually
select a point from each member of the set family. -/
def selectionOuterLimit (l : Filter ι) (s : ι → Set X) : Set X :=
  {x | ∃ f : ι → X, (∀ᶠ i in l, f i ∈ s i) ∧ MapClusterPt x l f}

@[simp]
theorem mem_kuratowskiOuterLimit {l : Filter ι} {s : ι → Set X} {x : X} :
    x ∈ kuratowskiOuterLimit l s ↔ ∀ A ∈ l, x ∈ closure (⋃ i ∈ A, s i) :=
  Iff.rfl

@[simp]
theorem mem_selectionOuterLimit {l : Filter ι} {s : ι → Set X} {x : X} :
    x ∈ selectionOuterLimit l s ↔
      ∃ f : ι → X, (∀ᶠ i in l, f i ∈ s i) ∧ MapClusterPt x l f :=
  Iff.rfl

/-- Every cluster point of an eventually admissible selection belongs to the
Painlevé–Kuratowski outer limit. -/
theorem selectionOuterLimit_subset_kuratowskiOuterLimit
    (l : Filter ι) (s : ι → Set X) :
    selectionOuterLimit l s ⊆ kuratowskiOuterLimit l s := by
  rintro x ⟨f, hf, hx⟩ A hA
  rw [mem_closure_iff_nhds]
  intro U hU
  have hFrequentlyU : ∃ᶠ i in l, f i ∈ U := hx.frequently hU
  have hEventuallyA : ∀ᶠ i in l, i ∈ A := hA
  rcases (hFrequentlyU.and_eventually (hEventuallyA.and hf)).exists with
    ⟨i, hiU, hiA, his⟩
  exact ⟨f i, hiU,
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, his⟩⟩⟩

end Filter

end MathlibAnalytic
end MGAP4D
