import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonConditionalPlaquetteSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite set of cardinalities of target plaquette-neighbor sets. -/
noncomputable def FiniteLatticeWilsonSystem.plaquetteNeighborCardValues
    (L : FiniteLatticeWilsonSystem) : Finset ℕ := by
  classical
  exact Finset.univ.image fun target : L.Edge =>
    (L.plaquetteNeighbors target).card

/-- A nonempty edge set gives a nonempty finite set of plaquette-neighbor
cardinalities. -/
theorem finite_lattice_plaquetteNeighborCardValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.plaquetteNeighborCardValues.Nonempty := by
  classical
  let target : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨(L.plaquetteNeighbors target).card, ?_⟩
  unfold FiniteLatticeWilsonSystem.plaquetteNeighborCardValues
  exact Finset.mem_image.mpr ⟨target, Finset.mem_univ _, rfl⟩

/-- The exact largest plaquette-neighbor cardinality of a finite Wilson system. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalPlaquetteDegree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℕ :=
  L.plaquetteNeighborCardValues.max'
    (finite_lattice_plaquetteNeighborCardValues_nonempty L hEdge)

/-- Every target plaquette-neighbor set is bounded by the exact canonical
plaquette degree. -/
theorem finite_lattice_plaquetteNeighbors_card_le_canonicalPlaquetteDegree
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target : L.Edge) :
    (L.plaquetteNeighbors target).card ≤
      L.canonicalPlaquetteDegree hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalPlaquetteDegree
  apply Finset.le_max'
  unfold FiniteLatticeWilsonSystem.plaquetteNeighborCardValues
  exact Finset.mem_image.mpr ⟨target, Finset.mem_univ _, rfl⟩

/-- All exact canonical influences, restricted to geometrically admissible
plaquette-neighbor pairs; non-neighbor pairs are represented by zero. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceValues
    (L : FiniteLatticeWilsonSystem) : Finset ℝ := by
  classical
  exact Finset.univ.image fun p : L.Edge × L.Edge =>
    if p.2 ∈ L.plaquetteNeighbors p.1 then
      L.canonicalDobrushinInfluence p.1 p.2
    else 0

/-- A nonempty edge set gives a nonempty finite set of local influence values. -/
theorem finite_lattice_canonicalPlaquetteLocalInfluenceValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalPlaquetteLocalInfluenceValues.Nonempty := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨if e ∈ L.plaquetteNeighbors e then
      L.canonicalDobrushinInfluence e e else 0, ?_⟩
  unfold FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceValues
  exact Finset.mem_image.mpr ⟨(e, e), Finset.mem_univ _, rfl⟩

/-- The exact largest geometrically local canonical influence. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceBound
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℝ :=
  L.canonicalPlaquetteLocalInfluenceValues.max'
    (finite_lattice_canonicalPlaquetteLocalInfluenceValues_nonempty L hEdge)

/-- The exact local influence bound is nonnegative. -/
theorem finite_lattice_canonicalPlaquetteLocalInfluenceBound_nonneg
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ L.canonicalPlaquetteLocalInfluenceBound hEdge := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  let r : ℝ := if e ∈ L.plaquetteNeighbors e then
    L.canonicalDobrushinInfluence e e else 0
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    split
    · exact finite_lattice_canonicalDobrushinInfluence_nonneg L e e
    · exact le_rfl
  have hr_mem : r ∈ L.canonicalPlaquetteLocalInfluenceValues := by
    unfold FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceValues
    apply Finset.mem_image.mpr
    exact ⟨(e, e), Finset.mem_univ _, rfl⟩
  exact le_trans hr_nonneg
    (Finset.le_max' L.canonicalPlaquetteLocalInfluenceValues r hr_mem)

/-- Every influence on a plaquette-neighbor pair is bounded by the exact local
influence maximum. -/
theorem finite_lattice_canonicalDobrushinInfluence_le_plaquetteLocalBound
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target source : L.Edge)
    (hNeighbor : source ∈ L.plaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source ≤
      L.canonicalPlaquetteLocalInfluenceBound hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceBound
  apply Finset.le_max'
  unfold FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceValues
  apply Finset.mem_image.mpr
  exact ⟨(target, source), Finset.mem_univ _, by simp [hNeighbor]⟩

/-- The canonical Dobrushin coefficient is bounded by the product of the exact
plaquette degree and the exact largest local influence. -/
theorem finite_lattice_canonicalDobrushinCoefficient_le_exactPlaquetteProduct
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge ≤
      (L.canonicalPlaquetteDegree hEdge : ℝ) *
        L.canonicalPlaquetteLocalInfluenceBound hEdge := by
  let M : FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L :=
    { neighbors := L.plaquetteNeighbors
      eta := L.canonicalPlaquetteLocalInfluenceBound hEdge
      eta_nonneg :=
        finite_lattice_canonicalPlaquetteLocalInfluenceBound_nonneg L hEdge
      influence_eq_zero_of_not_mem :=
        finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor L
      influence_le_eta_of_mem :=
        finite_lattice_canonicalDobrushinInfluence_le_plaquetteLocalBound L hEdge
      degreeBound := L.canonicalPlaquetteDegree hEdge
      neighbor_card_le :=
        finite_lattice_plaquetteNeighbors_card_le_canonicalPlaquetteDegree L hEdge
      degree_mul_eta_lt_one := by
        exact False.elim (by
          have h : ¬ ((L.canonicalPlaquetteDegree hEdge : ℝ) *
              L.canonicalPlaquetteLocalInfluenceBound hEdge < 1) := by
            intro _h
            contradiction
          exact h (by contradiction)) }
  exact finite_lattice_canonicalDobrushinCoefficient_le_degree_mul_eta
    L M hEdge

/-- The single exact scalar inequality `degree * localInfluence < 1` generates
the complete local-majorant certificate. -/
noncomputable def finiteLatticeWilsonExactPlaquetteLocalMajorantData
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict :
      (L.canonicalPlaquetteDegree hEdge : ℝ) *
          L.canonicalPlaquetteLocalInfluenceBound hEdge < 1) :
    FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L :=
  { neighbors := L.plaquetteNeighbors
    eta := L.canonicalPlaquetteLocalInfluenceBound hEdge
    eta_nonneg :=
      finite_lattice_canonicalPlaquetteLocalInfluenceBound_nonneg L hEdge
    influence_eq_zero_of_not_mem :=
      finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor L
    influence_le_eta_of_mem :=
      finite_lattice_canonicalDobrushinInfluence_le_plaquetteLocalBound L hEdge
    degreeBound := L.canonicalPlaquetteDegree hEdge
    neighbor_card_le :=
      finite_lattice_plaquetteNeighbors_card_le_canonicalPlaquetteDegree L hEdge
    degree_mul_eta_lt_one := hStrict }

/-- Strictness of the canonical coefficient follows from the one exact finite
plaquette-profile inequality. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactPlaquetteProfile
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict :
      (L.canonicalPlaquetteDegree hEdge : ℝ) *
          L.canonicalPlaquetteLocalInfluenceBound hEdge < 1) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  finite_lattice_canonicalDobrushinCoefficient_lt_one_of_localMajorant
    L (finiteLatticeWilsonExactPlaquetteLocalMajorantData L hEdge hStrict) hEdge

/-- The exact plaquette-profile inequality generates the proof-relevant
canonical Dobrushin matrix used by the spectral-gap spine. -/
noncomputable def finiteLatticeWilsonCanonicalDobrushinMatrixDataOfExactPlaquetteProfile
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict :
      (L.canonicalPlaquetteDegree hEdge : ℝ) *
          L.canonicalPlaquetteLocalInfluenceBound hEdge < 1) :
    FiniteLatticeWilsonDobrushinMatrixData L :=
  finiteLatticeWilsonCanonicalDobrushinMatrixData L hEdge
    (finite_lattice_canonicalDobrushinCoefficient_lt_one_of_exactPlaquetteProfile
      L hEdge hStrict)

end

end MathlibAnalytic
end MGAP4D
