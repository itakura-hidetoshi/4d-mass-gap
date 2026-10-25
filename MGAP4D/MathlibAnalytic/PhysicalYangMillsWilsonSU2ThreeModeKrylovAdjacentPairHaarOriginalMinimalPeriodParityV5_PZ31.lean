import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNondegenerateTripleGeometryV5_PZ30
import Mathlib.Tactic

/-!
# P4-Q2-PZ31 — minimal-period genuine triple-plaquette odd-edge support

PZ30 proves the genuine spatial SU(2) Wilson three-plaquette odd-edge
bound at all nonminimal even periods. The remaining minimal physical
side-two case (H=0) has 24 real spatial plaquettes, 24 physical links,
and pairwise overlapping same-plane plaquettes.

This file isolates an EXPLICIT, kernel-checked finite decidable
certificate for side two. The computable support uses the actual
PZ27 odd-edge proposition, not a proxy physical model. Its equality
with the original PZ28 Haar-support Finset is proved extensionally.
There is NO native_decide, new axiom, sorry, admit, synthetic
posterior, model replacement or Dobrushin argument.

NOTE: the decidable certificate is deliberately separated from the
measure-theoretic theorem transport, so failures of finite kernel
reduction are observable rather than hidden as assumptions.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators

set_option maxHeartbeats 29000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 1050000

/-- All equality tests in the genuine period-two geometry use
computable concrete ZMod-2, Fin-4, subtype and product deciders;
none use Classical.decEq. -/
local instance p4Q2PZ31_fullVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenVertex 0) :=
  Fintype.decidablePiFintype
local instance p4Q2PZ31_spatialVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceVertex 0) :=
  Subtype.instDecidableEq
local instance p4Q2PZ31_spatialDirectionDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirection :=
  Subtype.instDecidableEq
local instance p4Q2PZ31_spatialDirectionPairDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirectionPair :=
  Subtype.instDecidableEq
local instance p4Q2PZ31_linkDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceLink 0) :=
  instDecidableEqProd
local instance p4Q2PZ31_plaquetteDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSlicePlaquette 0) :=
  instDecidableEqProd

/-- The primary reflection plane is a computable equality of one
actual Euclidean-time ZMod-2 coordinate with zero. -/
local instance p4Q2PZ31_primaryPlaneDecidable :
    DecidablePred (periodicHypercubicEvenOnPrimaryReflectionPlane 0) :=
  fun v => inferInstanceAs (Decidable (v 0 = 0))

/-- Explicit COMPUTABLE enumeration of the real primary spatial
reflection plane, avoiding the inherited Fintype.ofFinite choice. -/
local instance p4Q2PZ31_spatialSliceVertexFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex 0) :=
  Fintype.subtype
    (Finset.univ.filter
      (periodicHypercubicEvenOnPrimaryReflectionPlane 0))
    (by intro v; simp)

/-- The three actual spatial directions and three ordered spatial
coordinate planes have directly filtered computable enumerations. -/
local instance p4Q2PZ31_spatialDirectionFintype :
    Fintype PeriodicHypercubicEvenSpatialDirection :=
  Fintype.subtype
    ((Finset.univ : Finset PeriodicHypercubicAxis).filter
      (fun mu => mu ≠ 0))
    (by intro mu; simp)
local instance p4Q2PZ31_spatialDirectionPairFintype :
    Fintype PeriodicHypercubicEvenSpatialDirectionPair :=
  Fintype.subtype
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenSpatialDirection ×
        PeriodicHypercubicEvenSpatialDirection)).filter
      (fun pair => pair.1.1 < pair.2.1))
    (by intro pair; simp)

local instance p4Q2PZ31_linkFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ31_plaqFintype :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section MinimalPeriod

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink 0
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette 0
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
local notation "Odd" => p4Q2PZ27_originalTripleOddEdge 0
local notation "OddSet" => p4Q2PZ28_originalOddEdges 0
local notation "Adm" => p4Q2PZ27_originalTwoLinkCoversOddEdges 0
local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar 0
local notation "Selected2" => p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar 0

/-- Constructively enumerated actual SU(2) odd-incidence spatial links at
physical side two. The predicates are exactly PZ27's real plaquette
four-edge membership, not a test-only surrogate. -/
def p4Q2PZ31_computablePeriodTwoOddEdges
    (p q r : Plaq) : Finset Link := by
  letI : DecidablePred (fun x : Link => Odd p q r x) := fun x => by
    unfold p4Q2PZ27_originalTripleOddEdge
      p4Q2PZ27_originalEdgeOnPlaquette
    infer_instance
  exact Finset.univ.filter (fun x : Link => Odd p q r x)

/-- Compare the explicitly enumerable Finset with the canonical PZ28
original physical odd-edge support, not its cardinality proxy. -/
theorem p4Q2PZ31_computablePeriodTwoOddEdges_eq_original
    (p q r : Plaq) :
    p4Q2PZ31_computablePeriodTwoOddEdges p q r =
      OddSet p q r := by
  classical
  ext x
  simp [p4Q2PZ31_computablePeriodTwoOddEdges,
    p4Q2PZ28_originalOddEdges]

/-- Exhaustive but KERNEL-CHECKED finite geometric statement. This is
a proof about all ordered triples of actual spatial period-two Wilson
plaquettes. No native evaluator or axiom is allowed. -/
private theorem p4Q2PZ31_minimalPeriodOddEdges_kernelCertificate :
    ∀ p q r : Plaq,
      p ≠ q → p ≠ r → q ≠ r →
        4 ≤ (p4Q2PZ31_computablePeriodTwoOddEdges p q r).card := by
  decide

/-- True original side-two finite even-periodic hypercubic geometry:
any three pairwise-distinct genuine spatial plaquettes have at least
four odd-incidence physical spatial links. -/
theorem p4Q2PZ31_originalMinimalTripleOddEdges_card_ge_four
    (p q r : Plaq)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    4 ≤ (OddSet p q r).card := by
  rw [← p4Q2PZ31_computablePeriodTwoOddEdges_eq_original p q r]
  exact p4Q2PZ31_minimalPeriodOddEdges_kernelCertificate p q r hpq hpr hqr

end MinimalPeriod
end GroundStatePosteriorJoint
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31_computablePeriodTwoOddEdges_eq_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31_originalMinimalTripleOddEdges_card_ge_four
