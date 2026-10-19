import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIWilsonKernelPosteriorEnvelopeV5_LS
import Mathlib.Tactic

/-!
# P4-Q2-LT — true interacting Wilson GI envelope-controlled local coercivity

LS bounds each original JH detector at a genuine boundary context z by
  A(z) = ||T||⁻¹ |s(z)| ||s⁻¹||_∞ (exp(16b) - exp(-16b)).
LR proves genuine local physical-Hilbert two-source coercivity with
  κ_p ≥ Δ_total² / (N_H² * 5 (||G_{e,z}||² + ||G_{e',z'}||²)).
The present theorem replaces both detector operator norms by their exact
LS envelopes, for the SAME LP-selected genuine plaquette and two true
interacting-Wilson boundary contexts.

The resulting strictly positive denominator is *derived* from the
original nonzero local GI minor; it is NOT assumed. The coefficient is
finite-volume, and its positive infimum over H is NOT claimed. The
actual transfer normalization and joint inverse half-density may depend
on H, as can the total determinant and plaquette count.

No posterior replacement by independent Haar, no artificial source or
rank, no Dobrushin hypothesis, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb

/-- Explicit true-Wilson LS envelope; all its H-dependent factors are
kept as actually defined in the physical one-slab transfer system. -/
noncomputable def p4Q2LT_originalGIContextEnvelope
    (z : Cfg × Cfg) : ℝ :=
  (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * |s z|) *
    (‖p4Q2LS_originalInverseJointSqrtContinuous H b hb‖ *
      p4Q2LS_originalPosteriorContrastEnvelope b)

local notation "A" => p4Q2LT_originalGIContextEnvelope H b hb

/-- Each true JH detector obeys the same exact LS envelope. -/
theorem p4Q2LT_originalGIResponse_norm_le_contextEnvelope
    (e : Link) (z : Cfg × Cfg) :
    ‖G e z‖ ≤ A z := by
  exact p4Q2LS_originalGIResponseCLM_norm_le_originalEnvelope H b hb e z

/-- No extra envelope-positivity hypothesis: it dominates a true norm. -/
theorem p4Q2LT_originalGIContextEnvelope_nonneg
    (e : Link) (z : Cfg × Cfg) :
    0 ≤ A z := by
  exact (norm_nonneg (G e z)).trans
    (p4Q2LT_originalGIResponse_norm_le_contextEnvelope H b hb e z)

/-- The pair of genuine squared operator norms is bounded by the pair
of squared original Wilson context envelopes, with the LR factor FIVE. -/
theorem p4Q2LT_originalGIOpNormSq_sum_le_envelopeSq_sum
    (e e' : Link) (z z' : Cfg × Cfg) :
    5 * (‖G e z‖^2 + ‖G e' z'‖^2) ≤
      5 * ((A z)^2 + (A z')^2) := by
  have h1 := p4Q2LT_originalGIResponse_norm_le_contextEnvelope H b hb e z
  have h2 := p4Q2LT_originalGIResponse_norm_le_contextEnvelope H b hb e' z'
  have h1pos := p4Q2LT_originalGIContextEnvelope_nonneg H b hb e z
  have h2pos := p4Q2LT_originalGIContextEnvelope_nonneg H b hb e' z'
  have hs1 : ‖G e z‖^2 ≤ (A z)^2 := by
    have hprod : 0 ≤ (A z - ‖G e z‖) * (A z + ‖G e z‖) :=
      mul_nonneg (sub_nonneg.mpr h1)
        (add_nonneg h1pos (norm_nonneg _))
    nlinarith [hprod]
  have hs2 : ‖G e' z'‖^2 ≤ (A z')^2 := by
    have hprod : 0 ≤ (A z' - ‖G e' z'‖) * (A z' + ‖G e' z'‖) :=
      mul_nonneg (sub_nonneg.mpr h2)
        (add_nonneg h2pos (norm_nonneg _))
    nlinarith [hprod]
  linarith

/-- The exact four-entry ORIGINAL local physical response denominator
inherits the Wilson kernel/posterior envelope through LR and LS. -/
theorem p4Q2LT_originalLocalGIFrobeniusSq_le_five_envelopeSq
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p ≤
      5 * ((A z)^2 + (A z')^2) := by
  exact (p4Q2LR_originalLocalGIFrobeniusSq_le_five_opNormSq
    H b hb e e' z z' p).trans
      (p4Q2LT_originalGIOpNormSq_sum_le_envelopeSq_sum
        H b hb e e' z z')

/-- Positivity of the LS envelope denominator is forced by an actual
nonzero two-context local minor; it is never a fresh assumption. -/
theorem p4Q2LT_originalGI_envelopeSq_sum_pos_of_local_minor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    0 < 5 * ((A z)^2 + (A z')^2) := by
  exact (p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
    H b hb e e' z z' p hminor).trans_le
      (p4Q2LT_originalGIOpNormSq_sum_le_envelopeSq_sum
        H b hb e e' z z')

/-- Full LS+LR+LQ quantitative statement on the SAME original
plaquette and TWO original Wilson interacting-posterior contexts:
  Δ_total² / (5 N_H² (A(z)² + A(z')²)) ≤ κ_p.
All denominator positivity follows from the original local minor. -/
theorem p4Q2LT_originalLocalGI_coercivity_ge_global_envelope_floor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0)
    (hcount : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (hAvg : |p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'| /
       (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
       |p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p|) :
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
      ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
        (5 * ((A z)^2 + (A z')^2))) ≤
      p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p := by
  let total := p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'
  let n : ℝ := (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
  let C : ℝ := 5 * (‖G e z‖^2 + ‖G e' z'‖^2)
  let D : ℝ := 5 * ((A z)^2 + (A z')^2)
  have hC : 0 < C :=
    p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
      H b hb e e' z z' p hminor
  have hCD : C ≤ D :=
    p4Q2LT_originalGIOpNormSq_sum_le_envelopeSq_sum
      H b hb e e' z z'
  have hD : 0 < D := lt_of_lt_of_le hC hCD
  have hn2 : 0 < n^2 := sq_pos_of_pos hcount
  have hCden : 0 < n^2 * C := mul_pos hn2 hC
  have hDden : 0 < n^2 * D := mul_pos hn2 hD
  have hden : n^2 * C ≤ n^2 * D :=
    mul_le_mul_of_nonneg_left hCD (sq_nonneg n)
  have hDiv : total^2 / (n^2 * D) ≤ total^2 / (n^2 * C) :=
    (div_le_div_iff₀ hDden hCden).2
      (mul_le_mul_of_nonneg_left hden (sq_nonneg total))
  have hLR :=
    p4Q2LR_originalLocalGI_coercivity_ge_global_opNorm_floor
      H b hb e e' z z' p hminor hcount hAvg
  exact hDiv.trans hLR

/-- Full genuine physical finite-H witness, with no artificial detector:
the LP-chosen original local plaquette has a positive coercivity
coefficient, the LS-controlled original-Wilson denominator is positive,
and the coercivity inequality holds on every original Gauss-law pair
x U + y W_p U. Neither κ_p nor the displayed floor is H-uniform. -/
theorem p4Q2LT_originalPhysicalLocalGI_exists_envelope_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < 5 * ((A z)^2 + (A z')^2) ∧
      0 < p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p ∧
      (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          (5 * ((A z)^2 + (A z')^2))) ≤
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hpos e e' left₀ right₀
  have hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  have hEnvelopePos :=
    p4Q2LT_originalGI_envelopeSq_sum_pos_of_local_minor
      H b hb e e' z z' p hlocal
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hlocal
  have hFloor :=
    p4Q2LT_originalLocalGI_coercivity_ge_global_envelope_floor
      H b hb e e' z z' p hlocal hn hAvg
  exact ⟨z, z', p, hp, hn, hEnvelopePos, hκ, hFloor, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalGIResponse_norm_le_contextEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalGIContextEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalGIOpNormSq_sum_le_envelopeSq_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalLocalGIFrobeniusSq_le_five_envelopeSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalGI_envelopeSq_sum_pos_of_local_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalLocalGI_coercivity_ge_global_envelope_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LT_originalPhysicalLocalGI_exists_envelope_floor
