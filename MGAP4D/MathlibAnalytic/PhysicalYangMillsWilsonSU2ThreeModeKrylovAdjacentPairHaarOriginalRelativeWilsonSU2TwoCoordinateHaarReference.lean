import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PairHaarCoordinateSupport
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSharpMaxColorWilsonHaarFloor
import Mathlib.Tactic

/-!
# P4-Q2-EG: actual two-coordinate residual sum and original Wilson Haar reference

EE established the true gauge-invariant SU(2) two-boundary relative-link
Wilson energy as a bounded continuous observable on the ACTUAL original
spatial pair configuration carrier, and gave distinct L2 classes for
the original Wilson–Perron joint law and independent pair-Haar law.

EF proved the actual independent pair-Haar CR coordinate projection fixes
that class at EVERY spatial coordinate except the selected left-link
Sum.inl e and right-link Sum.inr e. Here we sum the exact residuals using
the canonical full physical joint index I = Sum Link Link. The ENTIRE
all-coordinate pair-Haar L2 squared-defect energy of the true SU(2) relative
Wilson-energy observable is exactly the sum of its TWO genuine selected
coordinate defects: no other coordinate contributes.

We then instantiate EB's strictly positive TRUE physical original Wilson
Haar fiber-mass lower bound on the SAME concrete gauge-invariant SU(2)
bounded continuous Wilson observable. The earlier generic all-coordinate
comparison becomes an explicit real physical Wilson normalized twelve-color
Haar-reference lower bound on only the two selected genuine pair-Haar L2
coordinate residuals.

No synthetic probability, noncommutative interacting Wilson projection
commutation, positive selected-coordinate defect assertion, volume-uniform
lower estimate, or continuum mass-gap claim is introduced.
A physical original Wilson Haar REFERENCE is not identified with the
distinct normalized physical twelve-color conditional Dirichlet operator,
and an independent pair-Haar projection is not a Wilson conditional mean.
No new axiom, sorry, or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualOriginalWilsonTwoCoordinate

variable (H : ℕ)

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "I" => PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H 2
local notation "f" => p4Q2EE_SU2_pairHaarJointL2 H
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H

/-- For this actual SU(2) relative-link observable, the sum over ALL
physical pair-Haar coordinate defects is LITERALLY the two selected
left/right defects, without discarding or estimating any other term.
Each unused term vanishes by the TRUE EF CR projection theorem. -/
theorem p4Q2EG_SU2_allPairHaarDefects_eq_selectedTwo
    (e : Link) :
    (∑ i : I, ENNReal.ofReal (‖f e - P i (f e)‖ ^ 2)) =
      ENNReal.ofReal (‖f e - P (Sum.inl e) (f e)‖ ^ 2) +
        ENNReal.ofReal (‖f e - P (Sum.inr e) (f e)‖ ^ 2) := by
  classical
  let w : I → ENNReal :=
    fun i => ENNReal.ofReal (‖f e - P i (f e)‖ ^ 2)
  have hOff (i : I)
      (hL : i ≠ Sum.inl e) (hR : i ≠ Sum.inr e) :
      w i = 0 := by
    have hzero :=
      p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_defect_sq_zero
        H e i hL hR
    dsimp [w]
    rw [hzero, ENNReal.ofReal_zero]
  have hLeft :
      (∑ j : Link, w (Sum.inl j)) = w (Sum.inl e) := by
    apply Finset.sum_eq_single e
    · intro j _hj hne
      apply hOff (Sum.inl j)
      · simpa using hne
      · simp
    · intro hne
      exact (hne (Finset.mem_univ e)).elim
  have hRight :
      (∑ j : Link, w (Sum.inr j)) = w (Sum.inr e) := by
    apply Finset.sum_eq_single e
    · intro j _hj hne
      apply hOff (Sum.inr j)
      · simp
      · simpa using hne
    · intro hne
      exact (hne (Finset.mem_univ e)).elim
  change (∑ i : I, w i) = w (Sum.inl e) + w (Sum.inr e)
  calc
    (∑ i : I, w i) =
        (∑ j : Link, w (Sum.inl j)) +
          (∑ j : Link, w (Sum.inr j)) := by
      simp only [Fintype.sum_sum_type]
    _ = w (Sum.inl e) + w (Sum.inr e) := by
      rw [hLeft, hRight]

/-- An EXACT ORIGINAL physical Wilson Haar reference certificate for
the ACTUAL, gauge-invariant SU(2), relative-link BOUNDED CONTINUOUS
two-boundary observable. The true positive finite-H original Wilson
mass m>0 is UNCHANGED from DG/CP via EB. This is a proof about the genuine
Wilson reference (normalized 12-color sum), controlling exactly the
two selected independent pair-Haar L2 coordinate defects.

No strict positivity of those two residuals, and no volume-uniform
coefficient, is asserted here. -/
theorem p4Q2EG_SU2_originalWilsonReference_ge_selectedTwoHaarDefects
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m : ℝ, 0 < m ∧
      p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
        (ENNReal.ofReal (‖f e - P (Sum.inl e) (f e)‖ ^ 2) +
          ENNReal.ofReal (‖f e - P (Sum.inr e) (f e)‖ ^ 2)) ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference H 2
          (by norm_num) beta hbeta (fun z : Joint => F e z) := by
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2EB_originalWilsonTwelveReference_ge_maxColorHilbertDefects
      H 2 (by norm_num) beta hbeta
  have hStrong : StronglyMeasurable (fun z : Joint => F e z) :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F e z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have hAbs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [Real.norm_eq_abs] using hAbs
  have hEq :
      (fun z : Joint => F e z) =ᵐ[muPair]
        ((f e : Lp ℝ 2 muPair) : Joint → ℝ) :=
    (p4Q2EE_SU2_pairHaarJointL2_ae_eq H e).symm
  have hBoundReference :=
    hReference (f e) (fun z : Joint => F e z)
      hStrong 2 hBound hEq
  rw [p4Q2EG_SU2_allPairHaarDefects_eq_selectedTwo H e] at hBoundReference
  exact ⟨m, hm, hBoundReference⟩

end ActualOriginalWilsonTwoCoordinate
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EG_SU2_allPairHaarDefects_eq_selectedTwo
#print axioms MGAP4D.MathlibAnalytic.p4Q2EG_SU2_originalWilsonReference_ge_selectedTwoHaarDefects
