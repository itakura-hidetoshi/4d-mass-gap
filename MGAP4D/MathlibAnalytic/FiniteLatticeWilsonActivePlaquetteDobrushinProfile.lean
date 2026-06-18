import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonConditionalTotalVariationBounds

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The geometrically active source links for a target: plaquette neighbors with
the target itself removed.  Removing the diagonal is exact because the
canonical self-influence is zero. -/
noncomputable def FiniteLatticeWilsonSystem.activePlaquetteNeighbors
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) : Finset L.Edge := by
  classical
  exact (L.plaquetteNeighbors target).erase target

@[simp] theorem finite_lattice_mem_activePlaquetteNeighbors_iff
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) :
    source ∈ L.activePlaquetteNeighbors target ↔
      source ∈ L.plaquetteNeighbors target ∧ source ≠ target := by
  classical
  simp [FiniteLatticeWilsonSystem.activePlaquetteNeighbors, and_comm]

/-- The target itself never belongs to its active plaquette neighborhood. -/
@[simp] theorem finite_lattice_target_not_mem_activePlaquetteNeighbors
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) :
    target ∉ L.activePlaquetteNeighbors target := by
  classical
  simp [FiniteLatticeWilsonSystem.activePlaquetteNeighbors]

/-- Canonical influence vanishes outside the active plaquette neighborhood,
including both genuinely nonlocal sources and the exact zero diagonal. -/
theorem finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_activePlaquetteNeighbor
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge)
    (hNotActive : source ∉ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source = 0 := by
  classical
  by_cases hDiagonal : source = target
  · subst source
    exact finite_lattice_canonicalDobrushinInfluence_diagonal L target
  · have hNotNeighbor : source ∉ L.plaquetteNeighbors target := by
      intro hNeighbor
      exact hNotActive
        ((finite_lattice_mem_activePlaquetteNeighbors_iff
          L target source).2 ⟨hNeighbor, hDiagonal⟩)
    exact
      finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor
        L target source hNotNeighbor

/-- Active neighborhoods are no larger than the original plaquette-neighbor
sets. -/
theorem finite_lattice_activePlaquetteNeighbors_card_le_plaquetteNeighbors
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) :
    (L.activePlaquetteNeighbors target).card ≤
      (L.plaquetteNeighbors target).card := by
  classical
  unfold FiniteLatticeWilsonSystem.activePlaquetteNeighbors
  exact Finset.card_erase_le _ _

/-- The finite set of active plaquette-neighbor cardinalities. -/
noncomputable def FiniteLatticeWilsonSystem.activePlaquetteNeighborCardValues
    (L : FiniteLatticeWilsonSystem) : Finset ℕ := by
  classical
  exact Finset.univ.image fun target : L.Edge =>
    (L.activePlaquetteNeighbors target).card

/-- Nonempty edge sets give nonempty active-degree value sets. -/
theorem finite_lattice_activePlaquetteNeighborCardValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.activePlaquetteNeighborCardValues.Nonempty := by
  classical
  let target : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨(L.activePlaquetteNeighbors target).card, ?_⟩
  unfold FiniteLatticeWilsonSystem.activePlaquetteNeighborCardValues
  exact Finset.mem_image.mpr ⟨target, Finset.mem_univ _, rfl⟩

/-- The exact largest active plaquette-neighbor cardinality. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalActivePlaquetteDegree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℕ :=
  L.activePlaquetteNeighborCardValues.max'
    (finite_lattice_activePlaquetteNeighborCardValues_nonempty L hEdge)

/-- Every active target neighborhood is bounded by the exact active degree. -/
theorem finite_lattice_activePlaquetteNeighbors_card_le_canonicalActivePlaquetteDegree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target : L.Edge) :
    (L.activePlaquetteNeighbors target).card ≤
      L.canonicalActivePlaquetteDegree hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteDegree
  apply Finset.le_max'
  unfold FiniteLatticeWilsonSystem.activePlaquetteNeighborCardValues
  exact Finset.mem_image.mpr ⟨target, Finset.mem_univ _, rfl⟩

/-- The exact active degree is no larger than the earlier degree that included
the zero diagonal. -/
theorem finite_lattice_canonicalActivePlaquetteDegree_le_canonicalPlaquetteDegree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteDegree hEdge ≤
      L.canonicalPlaquetteDegree hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteDegree
  apply Finset.max'_le
  intro n hn
  unfold FiniteLatticeWilsonSystem.activePlaquetteNeighborCardValues at hn
  rcases Finset.mem_image.mp hn with ⟨target, _hTarget, rfl⟩
  exact le_trans
    (finite_lattice_activePlaquetteNeighbors_card_le_plaquetteNeighbors
      L target)
    (finite_lattice_plaquetteNeighbors_card_le_canonicalPlaquetteDegree
      L hEdge target)

/-- Exact canonical influences restricted to active off-diagonal plaquette
neighbors; all other pairs are represented by zero. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceValues
    (L : FiniteLatticeWilsonSystem) : Finset ℝ := by
  classical
  exact Finset.univ.image fun p : L.Edge × L.Edge =>
    if p.2 ∈ L.activePlaquetteNeighbors p.1 then
      L.canonicalDobrushinInfluence p.1 p.2
    else 0

/-- Nonempty edge sets give nonempty active influence-value sets. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteInfluenceValues.Nonempty := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨0, ?_⟩
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceValues
  apply Finset.mem_image.mpr
  exact ⟨(e, e), Finset.mem_univ _, by simp⟩

/-- The exact largest active off-diagonal plaquette influence. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceBound
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℝ :=
  L.canonicalActivePlaquetteInfluenceValues.max'
    (finite_lattice_canonicalActivePlaquetteInfluenceValues_nonempty L hEdge)

/-- The exact active local influence bound is nonnegative. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_nonneg
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ L.canonicalActivePlaquetteInfluenceBound hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceBound
  exact Finset.le_max'
    L.canonicalActivePlaquetteInfluenceValues 0
    (by
      let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
      unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceValues
      apply Finset.mem_image.mpr
      exact ⟨(e, e), Finset.mem_univ _, by simp⟩)

/-- Every influence on an active neighbor pair is bounded by the exact active
influence maximum. -/
theorem finite_lattice_canonicalDobrushinInfluence_le_activePlaquetteBound
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target source : L.Edge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source ≤
      L.canonicalActivePlaquetteInfluenceBound hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceBound
  apply Finset.le_max'
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceValues
  apply Finset.mem_image.mpr
  exact ⟨(target, source), Finset.mem_univ _, by simp [hActive]⟩

/-- The active influence bound is no larger than the earlier local influence
bound that included the zero diagonal. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_le_canonicalPlaquetteLocalInfluenceBound
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteInfluenceBound hEdge ≤
      L.canonicalPlaquetteLocalInfluenceBound hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceBound
  apply Finset.max'_le
  intro r hr
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteInfluenceValues at hr
  rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
  by_cases hActive : p.2 ∈ L.activePlaquetteNeighbors p.1
  · simp only [if_pos hActive]
    have hNeighbor : p.2 ∈ L.plaquetteNeighbors p.1 :=
      ((finite_lattice_mem_activePlaquetteNeighbors_iff
        L p.1 p.2).1 hActive).1
    exact finite_lattice_canonicalDobrushinInfluence_le_plaquetteLocalBound
      L hEdge p.1 p.2 hNeighbor
  · simp only [if_neg hActive]
    exact finite_lattice_canonicalPlaquetteLocalInfluenceBound_nonneg L hEdge

/-- Every canonical influence row is supported exactly on the active
neighborhood and bounded by active degree times active influence. -/
theorem finite_lattice_canonicalDobrushinRowSum_le_exactActivePlaquetteProduct
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤
      (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
        L.canonicalActivePlaquetteInfluenceBound hEdge := by
  classical
  have hSupport :
      (∑ source ∈ L.activePlaquetteNeighbors target,
          L.canonicalDobrushinInfluence target source) =
        ∑ source : L.Edge,
          L.canonicalDobrushinInfluence target source := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro source _hSource hNotActive
    exact
      finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_activePlaquetteNeighbor
        L target source hNotActive
  have hCard :
      ((L.activePlaquetteNeighbors target).card : ℝ) ≤
        (L.canonicalActivePlaquetteDegree hEdge : ℝ) := by
    exact_mod_cast
      finite_lattice_activePlaquetteNeighbors_card_le_canonicalActivePlaquetteDegree
        L hEdge target
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSum
  rw [← hSupport]
  calc
    (∑ source ∈ L.activePlaquetteNeighbors target,
        L.canonicalDobrushinInfluence target source) ≤
      ∑ _source ∈ L.activePlaquetteNeighbors target,
        L.canonicalActivePlaquetteInfluenceBound hEdge := by
          apply Finset.sum_le_sum
          intro source hSource
          exact
            finite_lattice_canonicalDobrushinInfluence_le_activePlaquetteBound
              L hEdge target source hSource
    _ = ((L.activePlaquetteNeighbors target).card : ℝ) *
        L.canonicalActivePlaquetteInfluenceBound hEdge := by
      simp [nsmul_eq_mul]
    _ ≤ (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
        L.canonicalActivePlaquetteInfluenceBound hEdge :=
      mul_le_mul_of_nonneg_right hCard
        (finite_lattice_canonicalActivePlaquetteInfluenceBound_nonneg L hEdge)

/-- The canonical coefficient admits the refined active-neighborhood product
bound. -/
theorem finite_lattice_canonicalDobrushinCoefficient_le_exactActivePlaquetteProduct
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge ≤
      (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
        L.canonicalActivePlaquetteInfluenceBound hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.max'_le
  intro r hr
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSums at hr
  rcases Finset.mem_image.mp hr with ⟨target, _hTarget, rfl⟩
  exact finite_lattice_canonicalDobrushinRowSum_le_exactActivePlaquetteProduct
    L hEdge target

/-- The refined active-profile inequality implies strict canonical Dobrushin
contraction. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactActivePlaquetteProfile
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict :
      (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
          L.canonicalActivePlaquetteInfluenceBound hEdge < 1) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  lt_of_le_of_lt
    (finite_lattice_canonicalDobrushinCoefficient_le_exactActivePlaquetteProduct
      L hEdge)
    hStrict

/-- The refined active-profile inequality generates the proof-relevant
canonical Dobrushin matrix. -/
noncomputable def
    finiteLatticeWilsonCanonicalDobrushinMatrixDataOfExactActivePlaquetteProfile
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict :
      (L.canonicalActivePlaquetteDegree hEdge : ℝ) *
          L.canonicalActivePlaquetteInfluenceBound hEdge < 1) :
    FiniteLatticeWilsonDobrushinMatrixData L :=
  finiteLatticeWilsonCanonicalDobrushinMatrixData L hEdge
    (finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactActivePlaquetteProfile
      L hEdge hStrict)

end

end MathlibAnalytic
end MGAP4D
