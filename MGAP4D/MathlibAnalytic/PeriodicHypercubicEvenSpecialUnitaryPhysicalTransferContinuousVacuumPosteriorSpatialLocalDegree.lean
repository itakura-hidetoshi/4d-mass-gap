import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRefinedLocalInfluence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import Mathlib.Tactic

/-!
# Volume-independent spatial plaquette-local posterior degree

The refined continuous-vacuum posterior influence separates into

* a direct coefficient on off-diagonal spatial-plaquette-local pairs;
* a response-generated coefficient on genuinely remote pairs.

The previous fixed-volume strictness arguments bounded all entries by a finite
total sum, so their scalar coefficient grew with the volume.  This file removes
that accumulation from the local part.

Intrinsic spatial plaquette locality means that target and source are touched
by one common spatial plaquette.  Under the canonical spatial-slice embedding,
every such off-diagonal source is therefore a full four-dimensional active
neighbor of the embedded target.  The existing hypercubic incidence theorem

  card(activeNeighbors target) <= 18

is volume independent.  Injectivity of the spatial-link embedding transfers
the same bound to intrinsic spatial-slice plaquette-local neighbors.

Consequently the complete local part of every refined posterior row (and,
by symmetry, every column) is bounded by

  18 * q_local(beta),

where

  q_local(beta) = (exp(32 beta)-1)/(exp(32 beta)+1).

This closes the local-degree component of the volume-uniformization problem.
No estimate of the remote contribution is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorSpatialLocalDegreeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorSpatialLocalDegreeSideLengthNeZero
    (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by
    change 2 * (H + 1) ≠ 0
    omega⟩

/-- Off-diagonal intrinsic spatial links sharing a spatial plaquette with the
fixed target. -/
noncomputable def
    periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter fun source =>
    source ≠ target ∧
      periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source

@[simp] theorem
    periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target ↔
      source ≠ target ∧
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source := by
  classical
  simp [periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors]

/-- Intrinsic spatial plaquette locality is symmetric. -/
theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocal_symm
    (H : ℕ)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hLocal :
      periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    periodicHypercubicEvenSpatialSlicePlaquetteLocal H source target := by
  rcases hLocal with ⟨p, hpTarget, hpSource⟩
  exact ⟨p, hpSource, hpTarget⟩

/-- Every intrinsic off-diagonal plaquette-local source embeds into the existing
full four-dimensional active-neighbor set. -/
theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbor_embedding_mem_activeNeighbors
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hSource :
      source ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H source ∈
      periodicHypercubicActiveNeighbors
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  classical
  rcases
      (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
        H target source).mp hSource with
    ⟨hNe, ⟨p, hpTarget, hpSource⟩⟩
  let fullPlaquette : PeriodicHypercubicPlaquette
      (PeriodicHypercubicEvenSideLength H) :=
    periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p
  let fullTarget : PeriodicHypercubicEdge
      (PeriodicHypercubicEvenSideLength H) :=
    periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let fullSource : PeriodicHypercubicEdge
      (PeriodicHypercubicEvenSideLength H) :=
    periodicHypercubicEvenSpatialSliceLinkEmbedding H source
  have hpTargetFull :
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H) fullPlaquette fullTarget := by
    simpa [
      fullPlaquette,
      fullTarget,
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink] using hpTarget
  have hpSourceFull :
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H) fullPlaquette fullSource := by
    simpa [
      fullPlaquette,
      fullSource,
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink] using hpSource
  have hpMem :
      fullPlaquette ∈
        periodicHypercubicTouchingPlaquettes
          (PeriodicHypercubicEvenSideLength H) fullTarget :=
    (periodicHypercubic_mem_touchingPlaquettes_iff
      (PeriodicHypercubicEvenSideLength H) fullTarget fullPlaquette).2
      hpTargetFull
  have hSourceEdge :
      fullSource ∈
        periodicHypercubicPlaquetteEdges
          (PeriodicHypercubicEvenSideLength H) fullPlaquette :=
    periodicHypercubic_mem_plaquetteEdges_of_touches
      (PeriodicHypercubicEvenSideLength H)
      fullPlaquette fullSource hpSourceFull
  have hFullNe : fullSource ≠ fullTarget := by
    intro hEq
    apply hNe
    exact
      periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H hEq
  have hOther :
      fullSource ∈
        periodicHypercubicPlaquetteOtherEdges
          (PeriodicHypercubicEvenSideLength H) fullTarget fullPlaquette := by
    unfold periodicHypercubicPlaquetteOtherEdges
    exact Finset.mem_erase.mpr ⟨hFullNe, hSourceEdge⟩
  unfold periodicHypercubicActiveNeighbors
  exact Finset.mem_biUnion.mpr ⟨fullPlaquette, hpMem, hOther⟩

/-- The intrinsic off-diagonal spatial plaquette-local degree is at most 18,
uniformly in the periodic side H. -/
theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors_card_le_eighteen
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target).card ≤
      18 := by
  classical
  let neighbors :=
    periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target
  let emb :=
    periodicHypercubicEvenSpatialSliceLinkEmbedding H
  let fullTarget :=
    periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let active :=
    periodicHypercubicActiveNeighbors
      (PeriodicHypercubicEvenSideLength H) fullTarget
  have hImageCard :
      (neighbors.image emb).card = neighbors.card :=
    Finset.card_image_of_injective neighbors
      (periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H)
  have hSubset : neighbors.image emb ⊆ active := by
    intro fullSource hMem
    rcases Finset.mem_image.mp hMem with ⟨source, hSource, rfl⟩
    exact
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbor_embedding_mem_activeNeighbors
        H target source hSource
  have hImageLe : (neighbors.image emb).card ≤ active.card :=
    Finset.card_le_card hSubset
  have hActive : active.card ≤ 18 := by
    dsimp [active, fullTarget]
    exact
      periodicHypercubicActiveNeighbors_card_le_eighteen
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
  have hLocal : neighbors.card ≤ 18 := by
    rw [← hImageCard]
    exact hImageLe.trans hActive
  simpa [neighbors] using hLocal

/-- Local part of one refined posterior row. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source ∈
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
      H beta epsilon target source

/-- On the local neighbor set every refined entry is exactly the direct local
coefficient, so the local row mass is cardinality times q_local. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass_eq_card_mul_direct
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass
        H beta epsilon target =
      ((periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors
          H target).card : ℝ) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass
  calc
    (∑ source ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta epsilon target source) =
      ∑ _source ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H target,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
      apply Finset.sum_congr rfl
      intro source hSource
      rcases
          (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
            H target source).mp hSource with
        ⟨hNe, hLocal⟩
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
        hNe, hLocal]
    _ =
      ((periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors
          H target).card : ℝ) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
      simp [nsmul_eq_mul]

/-- Volume-independent local row-mass bound for every refined posterior
influence profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass_le_eighteen_mul_direct
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass
        H beta epsilon target ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalRowMass_eq_card_mul_direct]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors_card_le_eighteen
        H target
  · exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
        beta hbeta

/-- Local part of one refined posterior column. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H source,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
      H beta epsilon target source

/-- By symmetry of spatial plaquette locality, every entry in the local column
set is also the direct local coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass_eq_card_mul_direct
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass
        H beta epsilon source =
      ((periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors
          H source).card : ℝ) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass
  calc
    (∑ target ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H source,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta epsilon target source) =
      ∑ _target ∈
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H source,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
      apply Finset.sum_congr rfl
      intro target hTarget
      rcases
          (periodicHypercubicEvenSpatialSlice_mem_plaquetteLocalNeighbors_iff
            H source target).mp hTarget with
        ⟨hNe, hLocal⟩
      have hLocal' :
          periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source :=
        periodicHypercubicEvenSpatialSlicePlaquetteLocal_symm H hLocal
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
        Ne.symm hNe, hLocal']
    _ =
      ((periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors
          H source).card : ℝ) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
      simp [nsmul_eq_mul]

/-- Volume-independent local column-mass bound for every refined posterior
influence profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass_le_eighteen_mul_direct
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass
        H beta epsilon source ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
          beta := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedLocalColumnMass_eq_card_mul_direct]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast
      periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors_card_le_eighteen
        H source
  · exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
        beta hbeta

end

end MathlibAnalytic
end MGAP4D
