import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverHaarRegionMarginV5_PZ37ABW
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapMomentCriterionV5_PZ37AAZ
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABX — alignment derived for the ACTUAL centered physical source

Keep the original FF physical receiver, both interacting Wilson posteriors,
Perron normalization, and the unchanged centered physical direction V_H.
First expose its two-update difference with the genuine positive denominator.
Then use the already proved finite-volume nonzero GI gap, not an assumed
receiver margin, to construct an actual aligned point. Swapping the two
auxiliary variables makes the temporal crossing strictly positive without
changing the signed pair. An orientation s in {1,-1} records the sign of
this SAME physical response; it does not replace the physical source.

Joint continuity and genuine Haar full support yield a rectangle A x V:
A is an OPEN positive outer boundary pair-Haar event; V is an OPEN positive
auxiliary two-copy Haar event; and on the whole rectangle
  s*(F_z(g)-F_z(h)) >= eta > 0,  cross_b(g,h) >= kappa > 0.
Consequently every z in A has the actual restricted signed-pair integral
  integral_V s*Phi_z >= eta*kappa*exp(-32*b)*Haar2(V) > 0.

IMPORTANT: V need not be ABV's fixed low/high cap. A,V,eta,kappa depend on
H,b and the genuine witness. This is not a volume-uniform input, a bound
on the ENTIRE negative tail, or a new proof of a uniform full GI gap.
The nonzero-gap input is discharged by AAZ only at fixed finite H,b>0.
No posterior, physical source, normalization or existing assumption changes.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "ν" => Measure.prod μ μ
local notation "cross" => p4Q2PZ37ABU_temporalCrossLog
local instance p4Q2PZ37ABX_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABX_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABX_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABX_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABX_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G
local instance p4Q2PZ37ABX_haarOpenPos : (normalizedCompactHaar G).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2PZ37ABX_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ABX_spatialOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ABX_outerOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance
local instance p4Q2PZ37ABX_outerProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "response" => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num)
local notation "pair" => p4Q2PZ37ABT_originalSignedPair H
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "O" => normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num)
local notation "W" => normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num)
local notation "Vinv" => normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num)

/-- A name for the difference of the SAME original FF physical response. -/
def p4Q2PZ37ABX_originalReceiverDifference
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (g h : G) : ℝ :=
  response b hb f e (z, g) - response b hb f e (z, h)
local notation "diff" => p4Q2PZ37ABX_originalReceiverDifference H

/-- Exact two-update formula; the order of the two joint receiver values
is reversed by FF's subtraction from the common original value. -/
theorem p4Q2PZ37ABX_originalDifference_eq_updateDifference
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (g h : G) :
    diff b hb f e z g h =
      (O b hb f (z.1, Function.update z.2 e h) -
        O b hb f (z.1, Function.update z.2 e g)) /
      (W b hb z * Vinv b hb z.2) := by
  unfold p4Q2PZ37ABX_originalReceiverDifference
  simp only [p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_apply]
  ring

/-- Genuine receiver sign is exactly the order of the actual two updated
joint receiver values, because its ORIGINAL denominator is positive. -/
theorem p4Q2PZ37ABX_originalDifference_nonneg_iff_updateOrder
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (g h : G) :
    0 ≤ diff b hb f e z g h ↔
      O b hb f (z.1, Function.update z.2 e g) ≤
        O b hb f (z.1, Function.update z.2 e h) := by
  rw [p4Q2PZ37ABX_originalDifference_eq_updateDifference]
  have hq := p4Q2FF_originalWilsonDensityCancellationWeight_pos H 2 (by norm_num) b hb z
  constructor
  · intro hd
    have hm := mul_nonneg hd hq.le
    rw [div_mul_cancel₀ _ hq.ne'] at hm
    exact sub_nonneg.mp hm
  · intro ho
    exact div_nonneg (sub_nonneg.mpr ho) hq.le

/-- Strict sign correspondence for the actual density determinant. -/
theorem p4Q2PZ37ABX_originalDet_pos_iff_cross_pos
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    0 < det b hb B e g h ↔ 0 < cross b g h := by
  constructor
  · intro hd
    by_contra hc
    have hs : 0 ≤ cross b h g := by
      rw [p4Q2PZ37ABU_temporalCrossLog_swap]
      exact neg_nonneg.mpr (le_of_not_gt hc)
    have hds := (p4Q2PZ37ABU_originalDet_nonneg_iff H b hb B e h g).mpr hs
    rw [p4Q2PZ37ABU_originalDet_swap] at hds
    linarith
  · intro hc
    exact (mul_pos (Real.exp_pos _) hc).trans_le
      (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb B e g h hc.le)

/-- A nonzero ACTUAL GI gap forces a genuine aligned two-point witness.
The sign records the gap orientation; the physical source is unchanged. -/
theorem p4Q2PZ37ABX_alignedPoint_of_nonzeroGI
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (hgap : gap b hb f e z ≠ 0) :
    ∃ (s : ℝ) (g h : G), (s = 1 ∨ s = -1) ∧
      0 < s * gap b hb f e z ∧ 0 < cross b g h ∧
      0 < s * diff b hb f e z g h := by
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < s * gap b hb f e z := by
    rcases lt_or_gt_of_ne hgap with hn | hp
    · exact ⟨-1, Or.inr rfl, by nlinarith⟩
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hp⟩
  obtain ⟨s, hsUnit, hsGap⟩ := hs
  have hi : (∫ w : G × G, pair b hb f e z w ∂ν) = 2 * gap b hb f e z := by
    have heq := p4Q2PZ37ABT_originalGI_eq_half_pair_integral H b hb f e z
    linarith
  have hIntegral : 0 < ∫ w : G × G, s * pair b hb f e z w ∂ν := by
    rw [integral_const_mul, hi]
    nlinarith
  have hPoint : ∃ w : G × G, 0 < s * pair b hb f e z w := by
    by_contra hn
    push_neg at hn
    have hnonpos : (∫ w : G × G, s * pair b hb f e z w ∂ν) ≤ 0 := integral_nonpos hn
    linarith
  obtain ⟨⟨g, h⟩, hp⟩ := hPoint
  have hp' : 0 < (s * diff b hb f e z g h) * det b hb z.2 e g h := by
    have heq : (s * diff b hb f e z g h) * det b hb z.2 e g h =
        s * pair b hb f e z (g, h) := by
      rw [p4Q2PZ37ABW_originalPair_eq_receiver_mul_det]
      unfold p4Q2PZ37ABX_originalReceiverDifference
      ring
    rw [heq]
    exact hp
  rcases mul_pos_iff.mp hp' with ⟨hF, hD⟩ | ⟨hF, hD⟩
  · exact ⟨s, g, h, hsUnit, hsGap,
      (p4Q2PZ37ABX_originalDet_pos_iff_cross_pos H b hb z.2 e g h).mp hD, hF⟩
  · have hDswap : 0 < det b hb z.2 e h g := by
      rw [p4Q2PZ37ABU_originalDet_swap]
      linarith
    have hFswap : 0 < s * diff b hb f e z h g := by
      unfold p4Q2PZ37ABX_originalReceiverDifference at hF ⊢
      nlinarith
    exact ⟨s, h, g, hsUnit, hsGap,
      (p4Q2PZ37ABX_originalDet_pos_iff_cross_pos H b hb z.2 e h g).mp hDswap, hFswap⟩

/-- Continuity uses the ORIGINAL bounded continuous FF receiver jointly
in all outer boundary variables and both inner group variables. -/
theorem p4Q2PZ37ABX_originalDifference_joint_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (s : ℝ) :
    Continuous (fun t : (Cfg × Cfg) × (G × G) =>
      s * diff b hb f e t.1 t.2.1 t.2.2) := by
  let F := response b hb f e
  have hg : Continuous (fun t : (Cfg × Cfg) × (G × G) => F (t.1, t.2.1)) :=
    F.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hh : Continuous (fun t : (Cfg × Cfg) × (G × G) => F (t.1, t.2.2)) :=
    F.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact continuous_const.mul (hg.sub hh)

/-- A model-derived local rectangle certificate, not an extra model axiom.
The theorem below constructs this data for the SAME centered physical source. -/
structure p4Q2PZ37ABX_OriginalAlignmentRectangle
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) where
  sign : ℝ
  orientation : sign = 1 ∨ sign = -1
  anchor : Cfg × Cfg
  outerEvent : Set (Cfg × Cfg)
  innerEvent : Set (G × G)
  eta : ℝ
  kappa : ℝ
  eta_pos : 0 < eta
  kappa_pos : 0 < kappa
  anchor_mem : anchor ∈ outerEvent
  anchor_gap_pos : 0 < sign * gap b hb f e anchor
  outer_open : IsOpen outerEvent
  inner_open : IsOpen innerEvent
  outer_mass_pos : 0 < Measure.real outer outerEvent
  inner_mass_pos : 0 < Measure.real ν innerEvent
  aligned : ∀ z ∈ outerEvent, ∀ w ∈ innerEvent,
    eta ≤ sign * diff b hb f e z w.1 w.2 ∧ kappa ≤ cross b w.1 w.2

/-- The actual nonzero GI gap generates positive receiver and crossing
margins on a product of two genuine positive-Haar OPEN regions. -/
theorem p4Q2PZ37ABX_alignmentRectangle_of_nonzeroGI
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z0 : Cfg × Cfg)
    (hgap : gap b hb f e z0 ≠ 0) :
    Nonempty (p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) := by
  obtain ⟨s, g, h, hs, hsGap, hc, hF⟩ :=
    p4Q2PZ37ABX_alignedPoint_of_nonzeroGI H b hb f e z0 hgap
  let eta : ℝ := s * diff b hb f e z0 g h / 2
  let kappa : ℝ := cross b g h / 2
  have heta : 0 < eta := half_pos hF
  have hkappa : 0 < kappa := half_pos hc
  let T : Set ((Cfg × Cfg) × (G × G)) :=
    {t | eta < s * diff b hb f e t.1 t.2.1 t.2.2 ∧ kappa < cross b t.2.1 t.2.2}
  have hTopen : IsOpen T :=
    (isOpen_lt continuous_const
      (p4Q2PZ37ABX_originalDifference_joint_continuous H b hb f e s)).inter
    (isOpen_lt continuous_const
      ((p4Q2PZ37ABV_temporalCrossLog_continuous b).comp continuous_snd))
  have hTmem : (z0, (g, h)) ∈ T := by
    change eta < s * diff b hb f e z0 g h ∧ kappa < cross b g h
    dsimp [eta, kappa]
    constructor <;> linarith
  obtain ⟨A0, hA0, S0, hS0, hsub⟩ := mem_nhds_prod_iff.mp (hTopen.mem_nhds hTmem)
  obtain ⟨A, hAA0, hAopen, hzA⟩ := mem_nhds_iff.mp hA0
  obtain ⟨S, hSS0, hSopen, hwS⟩ := mem_nhds_iff.mp hS0
  have hAmass : 0 < Measure.real outer A := by
    exact ENNReal.toReal_pos (hAopen.measure_pos outer ⟨z0, hzA⟩).ne'
      (measure_ne_top outer A)
  have hSmass : 0 < Measure.real ν S := by
    exact ENNReal.toReal_pos (hSopen.measure_pos ν ⟨(g, h), hwS⟩).ne'
      (measure_ne_top ν S)
  refine ⟨{ sign := s, orientation := hs, anchor := z0,
    outerEvent := A, innerEvent := S, eta := eta, kappa := kappa,
    eta_pos := heta, kappa_pos := hkappa, anchor_mem := hzA,
    anchor_gap_pos := hsGap, outer_open := hAopen, inner_open := hSopen,
    outer_mass_pos := hAmass, inner_mass_pos := hSmass, aligned := ?_ }⟩
  intro z hz w hw
  have ht : (z, w) ∈ T := hsub ⟨hAA0 hz, hSS0 hw⟩
  exact ⟨ht.1.le, ht.2.le⟩

/-- The certificate gives an actual ORIGINAL signed-pair floor. The sign
multiplier is handled algebraically, not by replacing the physical source. -/
theorem p4Q2PZ37ABX_alignmentRectangle_pair_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) (w : G × G) (hw : w ∈ R.innerEvent) :
    R.eta * R.kappa * Real.exp (-32 * b) ≤ R.sign * pair b hb f e z w := by
  have hA := R.aligned z hz w hw
  have hc : 0 ≤ cross b w.1 w.2 := R.kappa_pos.le.trans hA.2
  have hd : Real.exp (-32 * b) * R.kappa ≤ det b hb z.2 e w.1 w.2 :=
    (mul_le_mul_of_nonneg_left hA.2 (Real.exp_nonneg _)).trans
      (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb z.2 e w.1 w.2 hc)
  have hd0 : 0 ≤ det b hb z.2 e w.1 w.2 :=
    (mul_nonneg (Real.exp_nonneg _) R.kappa_pos.le).trans hd
  calc
    R.eta * R.kappa * Real.exp (-32 * b) =
        R.eta * (Real.exp (-32 * b) * R.kappa) := by ring
    _ ≤ R.eta * det b hb z.2 e w.1 w.2 :=
      mul_le_mul_of_nonneg_left hd R.eta_pos.le
    _ ≤ (R.sign * diff b hb f e z w.1 w.2) * det b hb z.2 e w.1 w.2 :=
      mul_le_mul_of_nonneg_right hA.1 hd0
    _ = R.sign * pair b hb f e z w := by
      rcases w with ⟨g, h⟩
      rw [p4Q2PZ37ABW_originalPair_eq_receiver_mul_det]
      unfold p4Q2PZ37ABX_originalReceiverDifference
      ring

/-- Uniform on the selected OUTER event, a strictly positive restricted
INNER Haar integral. This retains the actual original pair integrand. -/
theorem p4Q2PZ37ABX_alignmentRectangle_integral_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent ≤
      ∫ w in R.innerEvent, R.sign * pair b hb f e z w ∂ν := by
  exact setIntegral_ge_of_const_le_real R.inner_open.measurableSet
    (measure_ne_top _ _)
    (fun w hw => p4Q2PZ37ABX_alignmentRectangle_pair_lower H b hb f e R z hz w hw)
    ((p4Q2PZ37ABT_originalSignedPair_integrable H b hb f e z).const_mul R.sign).integrableOn

/-- UNCONDITIONAL at each finite H,b>0: an actual spatial link and a
positive-Haar rectangle of signed alignment for the UNCHANGED original
centered physical Wilson source. No new alignment hypothesis occurs. -/
theorem p4Q2PZ37ABX_exists_centeredPhysical_alignmentRectangle
    (b : ℝ) (hb : 0 < b) :
    ∃ e : Link, Nonempty (p4Q2PZ37ABX_OriginalAlignmentRectangle
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e) := by
  obtain ⟨e, hNotAE⟩ := p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero H b hb
  have hPoint : ∃ z : Cfg × Cfg,
      gap b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z ≠ 0 := by
    by_contra hn
    apply hNotAE
    have hz : ∀ z : Cfg × Cfg,
        gap b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z = 0 := by
      intro z
      by_contra hne
      exact hn ⟨z, hne⟩
    exact Filter.Eventually.of_forall hz
  obtain ⟨z, hz⟩ := hPoint
  exact ⟨e, p4Q2PZ37ABX_alignmentRectangle_of_nonzeroGI
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z hz⟩

/-- A strictly positive inner signed contribution on a positive actual
outer-Haar event is now constructed for the SAME source. Neither mass
nor margin is asserted H-uniform, and the full complement is still open. -/
theorem p4Q2PZ37ABX_exists_centeredPhysical_positiveRectangleIntegral
    (b : ℝ) (hb : 0 < b) :
    ∃ (e : Link) (R : p4Q2PZ37ABX_OriginalAlignmentRectangle
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e),
      ∀ z ∈ R.outerEvent, 0 <
        ∫ w in R.innerEvent,
          R.sign * pair b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z w ∂ν := by
  obtain ⟨e, ⟨R⟩⟩ := p4Q2PZ37ABX_exists_centeredPhysical_alignmentRectangle H b hb
  refine ⟨e, R, ?_⟩
  intro z hz
  have hpos : 0 < R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent :=
    mul_pos (mul_pos (mul_pos R.eta_pos R.kappa_pos) (Real.exp_pos _)) R.inner_mass_pos
  exact hpos.trans_le (p4Q2PZ37ABX_alignmentRectangle_integral_lower
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e R z hz)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_originalDifference_eq_updateDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_originalDifference_nonneg_iff_updateOrder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_originalDet_pos_iff_cross_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_alignedPoint_of_nonzeroGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_originalDifference_joint_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_alignmentRectangle_of_nonzeroGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_alignmentRectangle_pair_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_alignmentRectangle_integral_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_exists_centeredPhysical_alignmentRectangle
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABX_exists_centeredPhysical_positiveRectangleIntegral
