import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonConditionalLocalFactor

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A source link outside the target plaquette neighborhood cannot change the
target-local single-link Boltzmann factor. -/
theorem finite_lattice_targetLocalSingleLinkBoltzmannWeight_eq_of_not_neighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source)
    (g : L.Gauge) :
    L.targetLocalSingleLinkBoltzmannWeight A target g =
      L.targetLocalSingleLinkBoltzmannWeight B target g := by
  unfold FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
  rw [finite_lattice_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    L A B target source g hNotNeighbor hAgree]

/-- Consequently the target-local partition function is unchanged by modifying
a non-neighbor source link. -/
theorem finite_lattice_targetLocalSingleLinkPartitionFunction_eq_of_not_neighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalSingleLinkPartitionFunction A target =
      L.targetLocalSingleLinkPartitionFunction B target := by
  unfold FiniteLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
  apply tsum_congr
  intro g
  exact finite_lattice_targetLocalSingleLinkBoltzmannWeight_eq_of_not_neighbor
    L A B target source hNotNeighbor hAgree g

/-- The normalized target-local conditional law is insensitive to every source
link outside the target plaquette neighborhood. -/
theorem finite_lattice_targetLocalSingleLinkConditionalPMF_eq_of_not_neighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalSingleLinkConditionalPMF A target =
      L.targetLocalSingleLinkConditionalPMF B target := by
  ext g
  rw [finite_lattice_targetLocalSingleLinkConditionalPMF_apply,
    finite_lattice_targetLocalSingleLinkConditionalPMF_apply,
    finite_lattice_targetLocalSingleLinkBoltzmannWeight_eq_of_not_neighbor
      L A B target source hNotNeighbor hAgree g,
    finite_lattice_targetLocalSingleLinkPartitionFunction_eq_of_not_neighbor
      L A B target source hNotNeighbor hAgree]

/-- The concrete Wilson single-link conditional Gibbs law has exact plaquette
support: changing a non-neighbor source link leaves it unchanged. -/
theorem finite_lattice_singleLinkConditionalPMF_eq_of_not_plaquetteNeighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalPMF A target =
      L.singleLinkConditionalPMF B target := by
  rw [finite_lattice_singleLinkConditionalPMF_eq_targetLocal,
    finite_lattice_singleLinkConditionalPMF_eq_targetLocal]
  exact
    finite_lattice_targetLocalSingleLinkConditionalPMF_eq_of_not_neighbor
      L A B target source hNotNeighbor hAgree

/-- Hence the exact conditional total-variation response is zero outside the
plaquette-neighbor support. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_not_plaquetteNeighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalTotalVariation A B target = 0 := by
  classical
  have hPMF :
      L.singleLinkConditionalPMF A target =
        L.singleLinkConditionalPMF B target :=
    finite_lattice_singleLinkConditionalPMF_eq_of_not_plaquetteNeighbor
      L A B target source hNotNeighbor hAgree
  simp [FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation, hPMF]

/-- The exact canonical Dobrushin influence itself therefore vanishes outside
the geometric plaquette-neighbor set. -/
theorem finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source = 0 := by
  classical
  by_cases hDiagonal : target = source
  · subst source
    exact finite_lattice_canonicalDobrushinInfluence_diagonal L target
  · rw [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence,
      if_neg hDiagonal]
    apply le_antisymm
    · apply Finset.max'_le
      intro r hr
      unfold FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hr
      rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
      rw [finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_not_plaquetteNeighbor
        L p.1 (L.replaceLink p.1 source p.2) target source hNotNeighbor]
      intro e he
      simp [FiniteLatticeWilsonSystem.replaceLink, he]
    · have hNonneg :=
        finite_lattice_canonicalDobrushinInfluence_nonneg L target source
      simpa [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence,
        hDiagonal] using hNonneg

/-- Once the remaining local influence and neighborhood-cardinality estimates
are supplied, the concrete plaquette geometry generates the local majorant data
required by the canonical Dobrushin gap theorem. -/
noncomputable def finiteLatticeWilsonPlaquetteLocalMajorantData
    (L : FiniteLatticeWilsonSystem)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hLocal : ∀ target source : L.Edge,
      source ∈ L.plaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta)
    (degreeBound : ℕ)
    (hDegree : ∀ target : L.Edge,
      (L.plaquetteNeighbors target).card ≤ degreeBound)
    (hStrict : (degreeBound : ℝ) * eta < 1) :
    FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L :=
  { neighbors := L.plaquetteNeighbors
    eta := eta
    eta_nonneg := hEta
    influence_eq_zero_of_not_mem :=
      finite_lattice_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor L
    influence_le_eta_of_mem := hLocal
    degreeBound := degreeBound
    neighbor_card_le := hDegree
    degree_mul_eta_lt_one := hStrict }

end

end MathlibAnalytic
end MGAP4D
