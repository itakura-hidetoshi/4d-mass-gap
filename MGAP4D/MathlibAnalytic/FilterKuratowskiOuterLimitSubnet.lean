import MGAP4D.MathlibAnalytic.FilterKuratowskiOuterLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

universe u v

namespace FilterSet

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- Outer-limit points represented by a convergent selection over a refinement
filter on the graph carrier `ι × X`. -/
def convergentSelectionOuterLimit (l : Filter ι) (s : ι → Set X) : Set X :=
  {x | ∃ p : Filter (ι × X), p.NeBot ∧
    Tendsto Prod.fst p l ∧ Tendsto Prod.snd p (nhds x) ∧
      ∀ᶠ z in p, z.2 ∈ s z.1}

@[simp]
theorem mem_convergentSelectionOuterLimit {l : Filter ι} {s : ι → Set X} {x : X} :
    x ∈ convergentSelectionOuterLimit l s ↔
      ∃ p : Filter (ι × X), p.NeBot ∧
        Tendsto Prod.fst p l ∧ Tendsto Prod.snd p (nhds x) ∧
          ∀ᶠ z in p, z.2 ∈ s z.1 :=
  Iff.rfl

/-- Every convergent selection over a refinement filter is contained in the
filter Painlevé–Kuratowski outer limit. -/
theorem convergentSelectionOuterLimit_subset_kuratowskiOuterLimit
    (l : Filter ι) (s : ι → Set X) :
    convergentSelectionOuterLimit l s ⊆ kuratowskiOuterLimit l s := by
  rintro x ⟨p, hp, hIndex, hPoint, hMem⟩ A hA
  rw [mem_closure_iff_nhds]
  intro U hU
  letI : NeBot p := hp
  rcases ((hIndex hA).and ((hPoint hU).and hMem)).exists with
    ⟨z, hzA, hzU, hzs⟩
  exact ⟨z.2, hzU,
    Set.mem_iUnion.2 ⟨z.1, Set.mem_iUnion.2 ⟨hzA, hzs⟩⟩⟩

/-- A point in the filter Painlevé–Kuratowski outer limit admits a canonical
convergent-selection representation on `ι × X`. -/
theorem kuratowskiOuterLimit_subset_convergentSelectionOuterLimit
    (l : Filter ι) (s : ι → Set X) :
    kuratowskiOuterLimit l s ⊆ convergentSelectionOuterLimit l s := by
  intro x hx
  let graphSet : Set (ι × X) := {z | z.2 ∈ s z.1}
  let p : Filter (ι × X) :=
    (Filter.comap Prod.fst l ⊓ Filter.comap Prod.snd (nhds x)) ⊓
      Filter.principal graphSet
  have hBasis :
      p.HasBasis
        (fun AU : Set ι × Set X => AU.1 ∈ l ∧ AU.2 ∈ nhds x)
        (fun AU =>
          ((Prod.fst ⁻¹' AU.1) ∩ (Prod.snd ⁻¹' AU.2)) ∩ graphSet) := by
    simpa [p] using
      (((l.basis_sets.comap (Prod.fst : ι × X → ι)).inf
        ((nhds x).basis_sets.comap (Prod.snd : ι × X → X))).inf_principal graphSet)
  have hp : p.NeBot := hBasis.neBot_iff.2 (by
    intro AU hAU
    have hClosure := hx AU.1 hAU.1
    rw [mem_closure_iff_nhds] at hClosure
    rcases hClosure AU.2 hAU.2 with ⟨y, hyU, hyUnion⟩
    rcases Set.mem_iUnion.1 hyUnion with ⟨i, hyUnion⟩
    rcases Set.mem_iUnion.1 hyUnion with ⟨hiA, hyS⟩
    exact ⟨(i, y), ⟨⟨hiA, hyU⟩, hyS⟩⟩)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · exact (tendsto_iff_comap.2 (le_trans inf_le_left inf_le_left))
  · exact (tendsto_iff_comap.2 (le_trans inf_le_left inf_le_right))
  · exact le_principal_iff.mp inf_le_right

/-- The filter Painlevé–Kuratowski outer limit is exactly the set of limits of
convergent selections over refinement filters. -/
theorem kuratowskiOuterLimit_eq_convergentSelectionOuterLimit
    (l : Filter ι) (s : ι → Set X) :
    kuratowskiOuterLimit l s = convergentSelectionOuterLimit l s :=
  Set.Subset.antisymm
    (kuratowskiOuterLimit_subset_convergentSelectionOuterLimit l s)
    (convergentSelectionOuterLimit_subset_kuratowskiOuterLimit l s)

end FilterSet

end MathlibAnalytic
end MGAP4D
