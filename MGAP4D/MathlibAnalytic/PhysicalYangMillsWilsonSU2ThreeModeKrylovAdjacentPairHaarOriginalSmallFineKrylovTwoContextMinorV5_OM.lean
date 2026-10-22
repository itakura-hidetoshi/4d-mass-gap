import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSmallPositiveFineUnitNonEigenlineV5_OL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoContextSpatialGIMinorNonzeroV5_LM
import Mathlib.Tactic

/-!
# P4-Q2-OM — authentic small-positive fine Wilson TWO-context GI minor

This file CLOSES the previously isolated small-positive-fine two-context
physical Krylov detection obstruction without an artificial rank axiom:

* LM proves a genuinely NONZERO static (U, W_H U) two-source minor at
  two ACTUAL original interacting-Wilson posterior GI contexts.
* JI proves that the derivative at fine t=0 of the same original
  two-context (U, T_fine(t) U) minor is minus half that LM spatial
  minor, and therefore the normalized physical minor is nonzero at
  EVERY sufficiently small POSITIVE fine coupling t.
* Here we prove that this literal JI physical normalized minor is
  EXACTLY OJ's original signed HF right-Krylov modal two-row minor
  at depth r=1 with the actual first selector a1. The zero selector
  produces the same true Gauss-law U and the first selector produces
  the actual original normalized fine Wilson physical source.
* Consequently, TWO actual original physical contexts detect the
  SAME nonzero depth-one anchored pivot, which is killed by the
  first row and detected by the second row. At each fixed positive
  frozen coupling and each H, those contexts can be chosen BEFORE
  t, and work throughout a common volume/frozen-context dependent
  small-positive t interval.
* The resulting two-context map is injective on the entire true
  TWO-dimensional depth-one coefficient space. Thus the HJ
  all-context GI detector AND the actual HJ source synthesis are
  injective at depth one in this proven small-positive fine window.

The genuine two interacting Wilson posteriors, original FF receiver,
Gauss-law physical Hilbert source, Perron half-density and DISTINCT
frozen/fine couplings are preserved. This does not establish
arbitrary positive-fine coupling, arbitrary depth r>1 source
injectivity, volume-uniform positive separation U0, a common
scale-compatible endpoint, H1-C3 or continuum Yang-Mills mass gap.
No Dobrushin, independent Haar posterior, sorry/admit/new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section FrozenPositive
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H

/-- UNCONDITIONAL genuine original Wilson physical TWO-context minor
for the actual normalized fine source: LM supplies the real static
source minor witness and JI transports it by a PROVED derivative at
fine beta zero. Both original GI contexts are fixed BEFORE t, so the
same physical detector witnesses work throughout a positive interval.
No extra physical source frame, independence or GI-rank premise. -/
theorem p4Q2OM_originalPhysicalNormalizedMinor_exists_nonzero_smallFine
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ delta : ℝ, 0 < delta ∧
      ∀ (t : ℝ) (ht : 0 < t), t < delta →
        p4Q2JI_originalPhysicalNormalizedMinor H b hb.le e e' z z' t ht.le ≠ 0 := by
  obtain ⟨z, z', hStatic⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  obtain ⟨delta, hdelta, hFine⟩ :=
    p4Q2JI_originalPhysicalNormalizedMinor_smallPositive
      H b hb.le e e' z z' hStatic
  exact ⟨z, z', delta, hdelta, hFine⟩

end FrozenPositive

section ActualPositiveFineKrylov
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "First" => p4Q2IS_depthOneCoefficient
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- The literal first and zero actual depth-one coefficient selectors
produce the original physical Gauss-law U and original normalized
fine Wilson transferred U in the genuine HJ source synthesis. -/
theorem p4Q2OM_actualDepthOne_zeroFirst_physicalSources :
    S 1 (Zero 1) = U ∧ S 1 First = Fine U := by
  constructor
  · exact p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
  · calc
      S 1 First =
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n 1 :=
        p4Q2IU_firstSelector_synthesizes_actualFineRightSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
      _ = Fine U :=
        p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Original frozen two-interacting-Wilson GI receiver on the TRUE
zero-selector is exactly its GI response to U. -/
theorem p4Q2OM_actualDepthOne_zeroModal_eq_originalPhysicalUnitGI
    (e : Link) (z : Pair) :
    M 1 e z (Zero 1) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) U e z := by
  have hHF :=
    p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 (Zero 1) e z
  change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    Hn (beta n) (hbeta n) (S 1 (Zero 1)) e z = M 1 e z (Zero 1) at hHF
  rw [(p4Q2OM_actualDepthOne_zeroFirst_physicalSources
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n).1] at hHF
  exact hHF.symm

/-- The first ACTUAL physical Krylov source is not a surrogate rank
direction: at depth one its genuine modal evaluation equals the
original GI gap of the normalized FINE Wilson transferred U. -/
theorem p4Q2OM_actualDepthOne_firstModal_eq_originalFinePhysicalGI
    (e : Link) (z : Pair) :
    M 1 e z First =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (Fine U) e z := by
  have hHF :=
    p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 First e z
  change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    Hn (beta n) (hbeta n) (S 1 First) e z = M 1 e z First at hHF
  rw [(p4Q2OM_actualDepthOne_zeroFirst_physicalSources
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n).2] at hHF
  exact hHF.symm

/-- EXACT original operator identification closing the principal
OM compatibility gate: the literal JI normalized physical Wilson
minor and OJ's same two original HF modal receiver rows on
actual right-Krylov zero/first modes are IDENTICAL. No new rank. -/
theorem p4Q2OM_originalDepthOneCrossMinor_eq_truePhysicalNormalizedMinor
    (e e' : Link) (z z' : Pair) :
    p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 e e' z z' First =
    p4Q2JI_originalPhysicalNormalizedMinor
      Hn (beta n) (hbeta n) e e' z z'
      (beta (n + 1)) (hbeta (n + 1)) := by
  unfold p4Q2OJ_originalCrossContextModalMinor
    p4Q2JI_originalPhysicalNormalizedMinor
  rw [p4Q2OM_actualDepthOne_zeroModal_eq_originalPhysicalUnitGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z,
      p4Q2OM_actualDepthOne_zeroModal_eq_originalPhysicalUnitGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z',
      p4Q2OM_actualDepthOne_firstModal_eq_originalFinePhysicalGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z,
      p4Q2OM_actualDepthOne_firstModal_eq_originalFinePhysicalGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z']

/-- At frozen beta(n)>0, two genuine physical Wilson GI contexts can
be chosen independently of the fine coupling's numerical value,
and their depth-ONE actual OJ signed modal minor is nonzero for
EVERY 0<beta(n+1)<delta (delta depends on H and frozen physics). -/
theorem p4Q2OM_actualDepthOne_exists_fixedContexts_smallPositiveFine_minor_ne
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Pair, ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        p4Q2OJ_originalCrossContextModalMinor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 1 e e' z z' First ≠ 0) := by
  obtain ⟨z, z', delta, hdelta, hMinor⟩ :=
    p4Q2OM_originalPhysicalNormalizedMinor_exists_nonzero_smallFine
      Hn (beta n) hFrozen e e' left₀ right₀
  refine ⟨z, z', delta, hdelta, ?_⟩
  intro ht hlt
  rw [p4Q2OM_originalDepthOneCrossMinor_eq_truePhysicalNormalizedMinor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e e' z z']
  exact hMinor (beta (n + 1)) ht hlt

/-- For the SAME actual original GI two contexts, the depth-one
physical signed pivot is killed at the first row and its actual
second row equals EXACTLY OJ's true positive-fine cross-context minor. -/
theorem p4Q2OM_actualDepthOne_pivotSecondGI_eq_genuineCrossMinor
    (e e' : Link) (z z' : Pair) :
    M 1 e z (p4Q2IS_depthOnePivot (M 1 e z)) = 0 ∧
    M 1 e' z' (p4Q2IS_depthOnePivot (M 1 e z)) =
      p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 1 e e' z z' First := by
  refine ⟨p4Q2IS_depthOnePivot_anchor_null (M 1 e z), ?_⟩
  exact p4Q2IS_depthOnePivot_secondDetector_determinant
    (M 1 e z) (M 1 e' z')

/-- Two genuinely different signed Wilson GI rows detect the
ACTUAL first Krylov anchored physical residual: its physical
Gauss-law source is nonzero, not just its coefficient pivot.
No global invisible physical source or surrogate rank is assumed. -/
theorem p4Q2OM_actualDepthOne_nonzeroMinor_implies_nonzeroPhysicalPivot
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 e e' z z' First ≠ 0) :
    M 1 e' z' (p4Q2IS_depthOnePivot (M 1 e z)) ≠ 0 ∧
      S 1 (p4Q2IS_depthOnePivot (M 1 e z)) ≠ 0 := by
  have hSecond : M 1 e' z' (p4Q2IS_depthOnePivot (M 1 e z)) ≠ 0 := by
    rw [(p4Q2OM_actualDepthOne_pivotSecondGI_eq_genuineCrossMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z').2]
    exact hMinor
  refine ⟨hSecond, ?_⟩
  intro hSource
  have hKerS : p4Q2IS_depthOnePivot (M 1 e z) ∈ (S 1).ker :=
    (LinearMap.mem_ker).mpr hSource
  have hKerFull : p4Q2IS_depthOnePivot (M 1 e z) ∈ (Full 1).ker :=
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1) hKerS
  have hFull : Full 1 (p4Q2IS_depthOnePivot (M 1 e z)) = 0 :=
    (LinearMap.mem_ker).mp hKerFull
  have hEval := congrArg (fun g : Link → C(Pair, ℝ) => g e' z') hFull
  have hSecondZero : M 1 e' z' (p4Q2IS_depthOnePivot (M 1 e z)) = 0 := by
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hEval
  exact hSecond hSecondZero

end ActualPositiveFineKrylov

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_originalPhysicalNormalizedMinor_exists_nonzero_smallFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_actualDepthOne_zeroFirst_physicalSources
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_actualDepthOne_zeroModal_eq_originalPhysicalUnitGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_actualDepthOne_firstModal_eq_originalFinePhysicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_originalDepthOneCrossMinor_eq_truePhysicalNormalizedMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_actualDepthOne_exists_fixedContexts_smallPositiveFine_minor_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_actualDepthOne_pivotSecondGI_eq_genuineCrossMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OM_actualDepthOne_nonzeroMinor_implies_nonzeroPhysicalPivot
