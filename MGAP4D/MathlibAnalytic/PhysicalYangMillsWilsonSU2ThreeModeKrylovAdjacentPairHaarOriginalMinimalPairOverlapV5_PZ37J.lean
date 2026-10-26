import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPairOverlapGeometryV5_PZ37J
import Mathlib.Tactic

/-!
# PZ37J — actual period-two exceptional pair support, kernel checked

Enumerate the ORIGINAL primary spatial vertices, directions, planes and
four-edge supports with computable instances, as in PZ31. Kernel `decide`
proves that distinct period-two plaquettes share at most two links, and
that EXACTLY 48 ordered distinct pairs share two links. The computable
supports are proved equal to the original PZ28 supports before transport.

This is geometric support only. No nonzero amplitude or constancy of the
surviving diagonal/period-two Haar response is asserted.
-/
namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 29000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37J_min_fullVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenVertex 0) := Fintype.decidablePiFintype
local instance p4Q2PZ37J_min_spatialVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceVertex 0) := Subtype.instDecidableEq
local instance p4Q2PZ37J_min_directionDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirection := Subtype.instDecidableEq
local instance p4Q2PZ37J_min_planeDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirectionPair := Subtype.instDecidableEq
local instance p4Q2PZ37J_min_linkDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceLink 0) := instDecidableEqProd
local instance p4Q2PZ37J_min_plaqDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSlicePlaquette 0) := instDecidableEqProd
local instance p4Q2PZ37J_min_primaryPlaneDecidable :
    DecidablePred (periodicHypercubicEvenOnPrimaryReflectionPlane 0) :=
  fun v => inferInstanceAs (Decidable (v 0 = 0))
local instance p4Q2PZ37J_min_vertexFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex 0) :=
  Fintype.subtype
    (Finset.univ.filter (periodicHypercubicEvenOnPrimaryReflectionPlane 0))
    (by intro v; simp)
local instance p4Q2PZ37J_min_directionFintype :
    Fintype PeriodicHypercubicEvenSpatialDirection :=
  Fintype.subtype
    ((Finset.univ : Finset PeriodicHypercubicAxis).filter (fun mu => mu ≠ 0))
    (by intro mu; simp)
local instance p4Q2PZ37J_min_planeFintype :
    Fintype PeriodicHypercubicEvenSpatialDirectionPair :=
  Fintype.subtype
    ((Finset.univ : Finset (PeriodicHypercubicEvenSpatialDirection ×
      PeriodicHypercubicEvenSpatialDirection)).filter (fun d => d.1.1 < d.2.1))
    (by intro d; simp)
local instance p4Q2PZ37J_min_linkFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ37J_min_plaqFintype :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section MinimalPairGeometry
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink 0
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette 0
local notation "Four" => p4Q2PZ28_originalFourEdges 0

/-- Computable enumeration of the actual original four oriented links. -/
def p4Q2PZ37J_computableMinimalFourEdges (p : Plaq) : Finset Link :=
  {p4Q2PU3_originalPlaquetteEdge0 0 p, p4Q2PU3_originalPlaquetteEdge1 0 p,
    p4Q2PU3_originalPlaquetteEdge2 0 p, p4Q2PU3_originalPlaquetteEdge3 0 p}
local notation "CFour" => p4Q2PZ37J_computableMinimalFourEdges

/-- The finite enumeration is the original physical support, not a proxy. -/
theorem p4Q2PZ37J_computableMinimalFourEdges_eq_original (p : Plaq) :
    CFour p = Four p := by
  classical
  ext e
  simp [p4Q2PZ37J_computableMinimalFourEdges, p4Q2PZ28_originalFourEdges]

private theorem p4Q2PZ37J_minimalOverlap_kernelCertificate :
    ∀ p q : Plaq, p ≠ q → (CFour p ∩ CFour q).card ≤ 2 := by
  decide

/-- At period two no distinct pair has three shared original links. -/
theorem p4Q2PZ37J_originalMinimalOverlap_le_two
    (p q : Plaq) (hpq : p ≠ q) : (Four p ∩ Four q).card ≤ 2 := by
  rw [← p4Q2PZ37J_computableMinimalFourEdges_eq_original p,
    ← p4Q2PZ37J_computableMinimalFourEdges_eq_original q]
  exact p4Q2PZ37J_minimalOverlap_kernelCertificate p q hpq

/-- Ordered distinct pairs sharing exactly two actual original edges. -/
def p4Q2PZ37J_computableMinimalOverlapPairs : Finset (Plaq × Plaq) :=
  Finset.univ.filter (fun pq => pq.1 ≠ pq.2 ∧ (CFour pq.1 ∩ CFour pq.2).card = 2)

/-- Kernel-reduced count on the ACTUAL finite physical carriers, not native evaluation. -/
theorem p4Q2PZ37J_computableMinimalOverlapPairs_card :
    p4Q2PZ37J_computableMinimalOverlapPairs.card = 48 := by
  decide

/-- Canonical physical support formulation using the original four-edge sets. -/
noncomputable def p4Q2PZ37J_originalMinimalOverlapPairs : Finset (Plaq × Plaq) := by
  classical
  exact Finset.univ.filter (fun pq => pq.1 ≠ pq.2 ∧ (Four pq.1 ∩ Four pq.2).card = 2)

/-- Extensional equality transfers the enumerated count to original supports. -/
theorem p4Q2PZ37J_originalMinimalOverlapPairs_eq_computable :
    p4Q2PZ37J_originalMinimalOverlapPairs = p4Q2PZ37J_computableMinimalOverlapPairs := by
  classical
  ext pq
  simp [p4Q2PZ37J_originalMinimalOverlapPairs, p4Q2PZ37J_computableMinimalOverlapPairs,
    p4Q2PZ37J_computableMinimalFourEdges_eq_original]

/-- EXACTLY 48 ordered distinct genuine plaquette pairs survive the
geometric two-edge-overlap filter at H=0. No Haar amplitude claim. -/
theorem p4Q2PZ37J_originalMinimalOverlapPairs_card :
    p4Q2PZ37J_originalMinimalOverlapPairs.card = 48 := by
  rw [p4Q2PZ37J_originalMinimalOverlapPairs_eq_computable]
  exact p4Q2PZ37J_computableMinimalOverlapPairs_card

/-- The exceptional geometry actually exists; discarding H=0 by the
nonminimal overlap theorem would therefore lose real supported pairs. -/
theorem p4Q2PZ37J_originalMinimalOverlap_exists :
    ∃ p q : Plaq, p ≠ q ∧ (Four p ∩ Four q).card = 2 := by
  have hpos : 0 < p4Q2PZ37J_originalMinimalOverlapPairs.card := by
    rw [p4Q2PZ37J_originalMinimalOverlapPairs_card]
    decide
  obtain ⟨pq, hpq⟩ := Finset.card_pos.mp hpos
  exact ⟨pq.1, pq.2, (Finset.mem_filter.mp hpq).2⟩
end MinimalPairGeometry

section AllPeriodPairGeometry
variable (H : ℕ)
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Four" => p4Q2PZ28_originalFourEdges H
local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth H

/-- Off-diagonal original pair overlap is at most two at ALL finite H. -/
theorem p4Q2PZ37J_originalAllPeriodsOverlap_le_two
    (p q : Plaq) (hpq : p ≠ q) : (Four p ∩ Four q).card ≤ 2 := by
  by_cases hH : H = 0
  · subst H
    exact p4Q2PZ37J_originalMinimalOverlap_le_two p q hpq
  · have hh := p4Q2PZ30_originalPairOverlap_card_le_one H (by omega) p q hpq
    omega

/-- Any off-diagonal pair with enough shared support is NECESSARILY
minimal-period and shares EXACTLY two original links. -/
theorem p4Q2PZ37J_originalExceptionalOverlap_classification
    (p q : Plaq) (hpq : p ≠ q) (hOverlap : 2 ≤ (Four p ∩ Four q).card) :
    H = 0 ∧ (Four p ∩ Four q).card = 2 := by
  have hTwo := p4Q2PZ37J_originalAllPeriodsOverlap_le_two H p q hpq
  have hZero : H = 0 := by
    by_contra hH
    have hh := p4Q2PZ30_originalPairOverlap_card_le_one H (by omega) p q hpq
    omega
  exact ⟨hZero, by omega⟩

/-- Exact necessary geometry for a nonzero ORIGINAL full fourth-crossing
pair Haar integral. This does not claim either surviving class is nonzero. -/
theorem p4Q2PZ37J_originalPairFourth_nonzero_requires_diagonal_or_minimal
    (p q : Plaq) (B : Cfg) (hNonzero : Pair4 p q B ≠ 0) :
    p = q ∨ (H = 0 ∧ (Four p ∩ Four q).card = 2) := by
  by_cases hpq : p = q
  · exact Or.inl hpq
  · apply Or.inr
    apply p4Q2PZ37J_originalExceptionalOverlap_classification H p q hpq
    by_contra hOverlap
    exact hNonzero (p4Q2PZ37J_originalPairFourth_zero_of_overlap_le_one H p q B (by omega))
end AllPeriodPairGeometry
end GroundStatePosteriorJoint
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_computableMinimalFourEdges_eq_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalMinimalOverlap_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_computableMinimalOverlapPairs_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalMinimalOverlapPairs_eq_computable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalMinimalOverlapPairs_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalMinimalOverlap_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalAllPeriodsOverlap_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalExceptionalOverlap_classification
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPairFourth_nonzero_requires_diagonal_or_minimal
