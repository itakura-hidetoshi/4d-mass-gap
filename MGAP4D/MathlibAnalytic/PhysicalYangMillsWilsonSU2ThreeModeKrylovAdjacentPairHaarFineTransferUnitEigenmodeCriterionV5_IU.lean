import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonMinorPhysicalGramObstructionV5_IT
import Mathlib.Tactic

/-!
# P4-Q2-IU: genuine first fine Wilson transfer of the physical constant unit

At the first nonzero right-Krylov depth, the TRUE fine source is
  v1 = T_fine(physical Haar-L² constant unit),
where T_fine is the original **normalized physical Wilson one-slab transfer**
at the distinct fine coupling beta(n+1) >= 0, NOT the frozen detector beta(n).

Prove unconditionally that the original Wilson fine transfer has a STRICTLY
POSITIVE physical constant-unit inner product. In particular v1 != 0;
this is a genuine property of the positive interacting Wilson kernel.

An abstract two-mode kernel-compatibility lemma then identifies the
IS/IT anchored GI pivot source vanishing with the physical eigenline
condition: T_fine 1 is proportional to the SAME actual unit 1.

At frozen beta(n)>0, HY supplies a genuine original GI anchor.
For any such anchor:
  q_pivot = 0 IFF T_fine 1 lies in R*1,
  q_pivot > 0 IFF T_fine 1 lies outside R*1.
Thus the positive Gram obstruction in IT has an exact operator meaning.
If T_fine 1 is NOT an eigenline, the global original Wilson GL source
floor exists IFF a second genuinely interacting Wilson two-posterior
context has a nonzero 2x2 minor. If it IS an eigenline, the global floor
exists automatically (rank collapse is PHYSICAL, not GI invisibility).

This does NOT establish the original Wilson fine constant-unit eigenline
condition or its negation at positive fine coupling. No artificial frame,
Haar-conditional substitution, Dobrushin, volume/scale uniformity,
H1-C3, OS/continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IU_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A scalar detector that vanishes whenever the REAL synthesized
physical source vanishes cannot distinguish an actual source-dependent
linear relation. The anchored coefficient pivot is physical-zero IFF
the first synthesized source lies on the zero-source eigenline.

This does NOT assume either physical source is independent. -/
theorem p4Q2IU_abstract_anchorPivot_sourceZero_iff_sourceCollinear
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (S : E →ₗ[ℝ] F) (D : E →ₗ[ℝ] ℝ)
    (u v : E)
    (hCompatible : ∀ a : E, S a = 0 → D a = 0)
    (hAnchor : D u ≠ 0) :
    S (D u • v - D v • u) = 0 ↔
      ∃ t : ℝ, S v = t • S u := by
  constructor
  · intro hZero
    have hLin : D u • S v - D v • S u = 0 := by
      simpa only [map_sub, map_smul] using hZero
    have hEq : D u • S v = D v • S u := sub_eq_zero.mp hLin
    refine ⟨D v / D u, ?_⟩
    have hInv := congrArg (fun f : F => (D u)⁻¹ • f) hEq
    calc
      S v = (D u)⁻¹ • (D u • S v) := by
        simp [smul_smul, hAnchor]
      _ = (D u)⁻¹ • (D v • S u) := hInv
      _ = (D v / D u) • S u := by
        simp only [smul_smul, div_eq_mul_inv]
        congr 1
        ring
  · rintro ⟨t, ht⟩
    have hSource : S (v - t • u) = 0 := by
      rw [map_sub, map_smul, ht, sub_self]
    have hD : D (v - t • u) = 0 := hCompatible _ hSource
    have hDv : D v = t * D u := by
      simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hD
    calc
      S (D u • v - D v • u) =
          D u • S v - D v • S u := by
            rw [map_sub, map_smul, map_smul]
      _ = D u • (t • S u) - (t * D u) • S u := by rw [ht, hDv]
      _ = 0 := by
        rw [smul_smul, mul_comm (D u) t, sub_self]

section ActualRightDepthOne

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
local notation "Coeff" => Fin (1 + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "FullDetector" =>
  p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "FineTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "PhysicalUnit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The ACTUAL depth-one fine-right Krylov physical source equals
the ORIGINAL NORMALIZED fine Wilson one-slab transfer of the constant
gauge-invariant physical Haar-L² unit, at beta(n+1) (NOT beta(n)). -/
theorem p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit :
    RightFactor n 1 = FineTransfer PhysicalUnit := by
  change (FineTransfer ^ 1) PhysicalUnit = FineTransfer PhysicalUnit
  simp

/-- The real first-depth selector synthesizes exactly the genuine
first fine physical Wilson source, even without source independence. -/
theorem p4Q2IU_firstSelector_synthesizes_actualFineRightSource :
    PhysicalSource p4Q2IS_depthOneCoefficient = RightFactor n 1 := by
  change (∑ j : Fin (1 + 1),
    p4Q2IS_depthOneCoefficient j • RightFactor n (j : ℕ)) =
      RightFactor n 1
  apply Finset.sum_eq_single (1 : Fin (1 + 1))
  · intro j _hj hj
    simp [p4Q2IS_depthOneCoefficient, hj]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- The original interacting fine Wilson positive kernel gives an
UNCONDITIONAL strictly positive constant-unit overlap of the first
genuine Krylov physical source, for EVERY fine beta(n+1)>=0. -/
theorem p4Q2IU_actualFirstFineWilsonSource_unitOverlap_pos :
    0 < ⟪RightFactor n 1, RightFactor n 0⟫_ℝ := by
  have h0 : RightFactor n 0 = PhysicalUnit :=
    fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  rw [h0, p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
  rw [real_inner_smul_left]
  exact mul_pos
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))))
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_transfer_expectation_pos
      Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1)))

/-- The first ACTUAL fine Wilson source cannot itself vanish, for
ANY fine coupling including the strictly interacting positive sector.
This is strictly stronger than merely having a formal first coefficient. -/
theorem p4Q2IU_actualFirstFineWilsonSource_ne_zero :
    RightFactor n 1 ≠ 0 := by
  intro hZero
  have hPos := p4Q2IU_actualFirstFineWilsonSource_unitOverlap_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  rw [hZero, inner_zero_left] at hPos
  exact (not_lt_of_ge le_rfl) hPos

/-- On a TRUE nonzero HY original Wilson zero-depth anchor, the
physical pivot vanishes IFF the first true fine Wilson source
belongs to the constant-unit eigenline. This is the precise physical
rank-collapse branch left open by IS/IT, NOT an assumption that it holds. -/
theorem p4Q2IU_actualDepthOne_pivotPhysicalZero_iff_fineUnitEigenline
    (e : Link) (z : Pair)
    (hAnchor : Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0) :
    PhysicalSource (p4Q2IS_depthOnePivot (Modal e z)) = 0 ↔
      ∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit := by
  have hLe : (PhysicalSource).ker ≤ (FullDetector).ker :=
    p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
  have hCompat (a : Coeff) (hS : PhysicalSource a = 0) :
      Modal e z a = 0 := by
    have hPhi : FullDetector a = 0 :=
      (LinearMap.mem_ker).mp (hLe ((LinearMap.mem_ker).mpr hS))
    have hAt := congrArg (fun f : Link → C(Pair, ℝ) => f e z) hPhi
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hAt
  have hGeneric :=
    p4Q2IU_abstract_anchorPivot_sourceZero_iff_sourceCollinear
      PhysicalSource (Modal e z)
      (p4Q2GX_rightZeroCoefficient 1) p4Q2IS_depthOneCoefficient
      hCompat hAnchor
  have h0 : PhysicalSource (p4Q2GX_rightZeroCoefficient 1) = PhysicalUnit :=
    p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
  have h1 : PhysicalSource p4Q2IS_depthOneCoefficient =
      FineTransfer PhysicalUnit := by
    rw [p4Q2IU_firstSelector_synthesizes_actualFineRightSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
    exact p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  simpa only [p4Q2IS_depthOnePivot, h0, h1] using hGeneric

/-- Exact positive physical Haar-L² source Gram criterion for a genuine
Wilson anchor, stated in terms of the ACTUAL normalized fine Wilson
unit eigenline instead of an unverified first-mode frame condition. -/
theorem p4Q2IU_actualDepthOne_pivotGram_pos_iff_fineUnit_notEigenline
    (e : Link) (z : Pair)
    (hAnchor : Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0) :
    (0 < star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
      (Qsrc *ᵥ p4Q2IS_depthOnePivot (Modal e z))) ↔
      ¬ (∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit) := by
  have hPos :=
    p4Q2IT_actualDepthOne_pivot_physicalGram_pos_iff_source_nonzero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (Modal e z)
  exact hPos.trans
    (not_congr
      (p4Q2IU_actualDepthOne_pivotPhysicalZero_iff_fineUnitEigenline
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z hAnchor))

/-- For the actual depth-one Wilson source, the entire positive-fine
physical rank obstruction can be rewritten as failure of the
constant-unit eigenline condition, WITHOUT changing the actual original
interacting posterior GI detector. -/
theorem p4Q2IU_actualDepthOne_invisible_iff_fineUnit_nonEigen_and_noMinors
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ z : Pair,
      Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
      (p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1 ≠ ⊥ ↔
        (¬ ∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit) ∧
        (∀ e' : Link, ∀ z' : Pair,
          p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') = 0)) := by
  obtain ⟨z, hAnchor, hObstruction⟩ :=
    p4Q2IT_actualDepthOne_invisibleSector_iff_positivePhysicalGram_and_allWilsonMinors_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨z, hAnchor, ?_⟩
  exact hObstruction.trans
    (and_congr
      (p4Q2IU_actualDepthOne_pivotGram_pos_iff_fineUnit_notEigenline
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z hAnchor) Iff.rfl)

/-- The strictly positive ORIGINAL Wilson GL source-norm floor on ALL
physical r=1 sources exists iff the normalized FINE Wilson one-slab
transfer has the constant-unit eigenline OR two actual interacting
Wilson GI pair-context response rows have NONZERO determinant.
This is a true finite model exact alternative; no side is asserted
to hold at positive fine beta. -/
theorem p4Q2IU_actualDepthOne_globalGLFloor_iff_fineUnitEigen_or_WilsonMinor
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ z : Pair,
      Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
      ((∃ c : ℝ, 0 < c ∧
          ∀ f : ↥((PhysicalSource).range),
            c * ‖(f : Phys)‖ ^ 2 ≤
              OriginalMass (f : Phys) (Finset.univ : Finset Link)) ↔
        (∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit) ∨
        (∃ e' : Link, ∃ z' : Pair,
          p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') ≠ 0)) := by
  obtain ⟨z, hAnchor, hFloor⟩ :=
    p4Q2IT_actualDepthOne_globalOriginalGLFloor_iff_zeroPhysicalPivot_or_nonzeroWilsonMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨z, hAnchor, ?_⟩
  have hQzero :
      (star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
        (Qsrc *ᵥ (p4Q2IS_depthOnePivot (Modal e z))) = 0) ↔
        (∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit) :=
    (p4Q2IT_actualDepthOne_pivot_physicalGram_zero_iff_source_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (Modal e z)).trans
      (p4Q2IU_actualDepthOne_pivotPhysicalZero_iff_fineUnitEigenline
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z hAnchor)
  exact hFloor.trans (or_congr hQzero Iff.rfl)

end ActualRightDepthOne
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_abstract_anchorPivot_sourceZero_iff_sourceCollinear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualFirstRightSource_eq_normalizedFineWilsonUnit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_firstSelector_synthesizes_actualFineRightSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualFirstFineWilsonSource_unitOverlap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualFirstFineWilsonSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualDepthOne_pivotPhysicalZero_iff_fineUnitEigenline
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualDepthOne_pivotGram_pos_iff_fineUnit_notEigenline
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualDepthOne_invisible_iff_fineUnit_nonEigen_and_noMinors
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IU_actualDepthOne_globalGLFloor_iff_fineUnitEigen_or_WilsonMinor
