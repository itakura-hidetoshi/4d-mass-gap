import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeTransferSymmetryV5_PZ37ACB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOptimizedMismatchCertificateV5_PZ37ACA

/-!
# P4-Q2-PZ37ACB — actual gauge-orbit mismatch and all-context obstruction

Use the proved genuine center-gauge transport of the SAME centered
Gauss-law receiver, and the exact SU(2) identity E(c*g)=2-E(g). Genuine
two-copy Haar change of variables exchanges the full cross-part masses:
M_s(Gamma z)=M_{-s}(z). Receiver and transfer-section covariance change
sign, their variances and regression defects agree, and the actual ACA
optimal budgets exchange orientation.

ABX supplies an active original link at each finite H,b>0. On that link,
no fixed orientation can satisfy M_{-s} <= theta*M_s at EVERY outer
context for any theta<1. In particular each orientation has a context
with strictly positive actual mismatch. These conclusions are derived
from the original source and genuine positive rectangle, not an assumed
failure of alignment. They do not exclude bounds on a selected outer
event. No sign symmetry of GI or of its two fixed posterior anchors is
asserted, and no volume-uniform coercivity follows.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "c" => p4Q2PZ35D4_centralMinusOne
local notation "μ" => normalizedCompactHaar G
local notation "ν" => Measure.prod μ μ
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACB_mismatchGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACB_mismatchCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACB_mismatchCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACB_mismatchMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACB_mismatchBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACB_mismatchProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

private theorem p4Q2PZ37ACB_pairHaar_central_integral
    (q : G × G → ℝ) (hq : Continuous q) :
    (∫ w : G × G, q (c * w.1, c * w.2) ∂ν) = ∫ w : G × G, q w ∂ν := by
  have hm : MeasurePreserving (fun g : G => c * g) μ μ := by
    simpa only [mul_one] using
      normalizedCompactHaar_measurePreserving_mul_left_right G c (1 : G)
  let T : G × G → G × G := fun w => (c * w.1, c * w.2)
  have hp : MeasurePreserving T ν ν := hm.prod hm
  have hi : (∫ w : G × G, q w ∂Measure.map T ν) =
      ∫ w : G × G, q (T w) ∂ν :=
    integral_map_of_stronglyMeasurable hp.measurable hq.stronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

private theorem p4Q2PZ37ACB_antipodal_moments
    (Q R : G → ℝ) (hQ : Continuous Q) (hR : Continuous R)
    (hTrans : ∀ g, R g = Q (c * g)) :
    Cov R E = -Cov Q E ∧ Var R = Var Q := by
  have hE := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have hC :
      (∫ w : G × G, (R w.1 - R w.2) * (E w.1 - E w.2) ∂ν) =
        -(∫ w : G × G, (Q w.1 - Q w.2) * (E w.1 - E w.2) ∂ν) := by
    calc
      _ = ∫ w : G × G,
          (R (c * w.1) - R (c * w.2)) * (E (c * w.1) - E (c * w.2)) ∂ν :=
        (p4Q2PZ37ACB_pairHaar_central_integral _
          (((hR.comp continuous_fst).sub (hR.comp continuous_snd)).mul
            ((hE.comp continuous_fst).sub (hE.comp continuous_snd)))).symm
      _ = ∫ w : G × G, -((Q w.1 - Q w.2) * (E w.1 - E w.2)) ∂ν := by
        apply integral_congr_ae
        filter_upwards with w
        simp only [hTrans, ← mul_assoc, p4Q2PZ37ABV_centralMinusOne_mul_self,
          one_mul, p4Q2PZ37ABV_central_mul_energy]
        ring
      _ = _ := integral_neg _
  have hV :
      (∫ w : G × G, (R w.1 - R w.2) ^ 2 ∂ν) =
        ∫ w : G × G, (Q w.1 - Q w.2) ^ 2 ∂ν := by
    calc
      _ = ∫ w : G × G, (R (c * w.1) - R (c * w.2)) ^ 2 ∂ν :=
        (p4Q2PZ37ACB_pairHaar_central_integral _
          (((hR.comp continuous_fst).sub (hR.comp continuous_snd)).pow 2)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with w
        simp only [hTrans, ← mul_assoc, p4Q2PZ37ABV_centralMinusOne_mul_self, one_mul]
  rw [CompactEnergyMismatchMoment.difference_product_integral μ R E hR hE,
    CompactEnergyMismatchMoment.difference_product_integral μ Q E hQ hE] at hC
  rw [CompactEnergyMismatchMoment.difference_square_integral μ R hR,
    CompactEnergyMismatchMoment.difference_square_integral μ Q hQ] at hV
  constructor <;> linarith

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "fH" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "Γ" => p4Q2PZ37ACB_originalCenterGaugePair H
local notation "psi" => p4Q2PZ37ABY_originalCrossPair H
local notation "mass" => p4Q2PZ37ABY_originalCrossPartMass H
local notation "budget" => p4Q2PZ37ACA_originalOptimizedMismatchBound H
local instance p4Q2PZ37ACB_mismatchLinks : Fintype Link := Fintype.ofFinite _

private theorem p4Q2PZ37ACB_centeredReceiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb fH e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb fH e).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The true centered-source receiver covariance reverses under the
genuine central gauge transformation of the two outer boundaries. -/
theorem p4Q2PZ37ACB_centeredReceiver_covariance_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Cov (F b hb fH e (Γ e z)) E = -Cov (F b hb fH e z) E := by
  exact (p4Q2PZ37ACB_antipodal_moments
    (F b hb fH e z) (F b hb fH e (Γ e z))
    (p4Q2PZ37ACB_centeredReceiver_continuous H b hb e z)
    (p4Q2PZ37ACB_centeredReceiver_continuous H b hb e (Γ e z))
    (p4Q2PZ37ACB_centeredReceiver_centerGauge H b hb e z)).1

/-- The original centered receiver variance is preserved exactly. -/
theorem p4Q2PZ37ACB_centeredReceiver_variance_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Var (F b hb fH e (Γ e z)) = Var (F b hb fH e z) := by
  exact (p4Q2PZ37ACB_antipodal_moments
    (F b hb fH e z) (F b hb fH e (Γ e z))
    (p4Q2PZ37ACB_centeredReceiver_continuous H b hb e z)
    (p4Q2PZ37ACB_centeredReceiver_continuous H b hb e (Γ e z))
    (p4Q2PZ37ACB_centeredReceiver_centerGauge H b hb e z)).2

/-- The SAME actual Perron transfer-section energy covariance reverses. -/
theorem p4Q2PZ37ACB_centeredTransfer_covariance_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Cov (U b hb fH e (Γ e z)) E = -Cov (U b hb fH e z) E := by
  exact (p4Q2PZ37ACB_antipodal_moments
    (U b hb fH e z) (U b hb fH e (Γ e z))
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb fH e z)
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb fH e (Γ e z))
    (p4Q2PZ37ACB_centeredTransferSection_centerGauge H b hb e z)).1

/-- The actual transfer-section variance retains all true Perron factors. -/
theorem p4Q2PZ37ACB_centeredTransfer_variance_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Var (U b hb fH e (Γ e z)) = Var (U b hb fH e z) := by
  exact (p4Q2PZ37ACB_antipodal_moments
    (U b hb fH e z) (U b hb fH e (Γ e z))
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb fH e z)
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb fH e (Γ e z))
    (p4Q2PZ37ACB_centeredTransferSection_centerGauge H b hb e z)).2

/-- The actual receiver regression defect is constant on this gauge orbit. -/
theorem p4Q2PZ37ACB_centeredReceiver_defect_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Var (F b hb fH e (Γ e z)) - 4 * (Cov (F b hb fH e (Γ e z)) E) ^ 2 =
      Var (F b hb fH e z) - 4 * (Cov (F b hb fH e z) E) ^ 2 := by
  rw [p4Q2PZ37ACB_centeredReceiver_variance_centerGauge,
    p4Q2PZ37ACB_centeredReceiver_covariance_centerGauge, neg_sq]

/-- The original transfer regression defect obeys the identical invariance. -/
theorem p4Q2PZ37ACB_centeredTransfer_defect_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Var (U b hb fH e (Γ e z)) - 4 * (Cov (U b hb fH e (Γ e z)) E) ^ 2 =
      Var (U b hb fH e z) - 4 * (Cov (U b hb fH e z) E) ^ 2 := by
  rw [p4Q2PZ37ACB_centeredTransfer_variance_centerGauge,
    p4Q2PZ37ACB_centeredTransfer_covariance_centerGauge, neg_sq]

/-- The original ACA optimal budget exchanges orientation on the genuine
gauge orbit; no correlation sign or tail cap is supplied as a premise. -/
theorem p4Q2PZ37ACB_centeredOptimizedBudget_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    budget b hb fH e (Γ e z) s = budget b hb fH e z (-s) := by
  unfold p4Q2PZ37ACA_originalOptimizedMismatchBound CompactEnergyMismatchMoment.optimalBudget
  rw [p4Q2PZ37ACB_centeredReceiver_variance_centerGauge,
    p4Q2PZ37ACB_centeredReceiver_covariance_centerGauge]
  ring

/-- Actual FF receiver/energy crossing under genuine center-gauge transport.
Only the auxiliary Haar variables are changed on the right-hand side. -/
theorem p4Q2PZ37ACB_centeredCrossPair_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (s : ℝ) (w : G × G) :
    psi b hb fH e (Γ e z) s w = psi b hb fH e z (-s) (c * w.1, c * w.2) := by
  simp only [p4Q2PZ37ABY_originalCrossPair_eq_energy]
  change (2 * b) * (s * (F b hb fH e (Γ e z) w.1 - F b hb fH e (Γ e z) w.2) *
      (E w.2 - E w.1)) =
    (2 * b) * ((-s) * (F b hb fH e z (c * w.1) - F b hb fH e z (c * w.2)) *
      (E (c * w.2) - E (c * w.1)))
  simp only [p4Q2PZ37ACB_centeredReceiver_centerGauge,
    p4Q2PZ37ABV_central_mul_energy]
  ring

/-- BOTH full original cross-part masses exchange under this real gauge
orbit. No region of either tail is omitted and no posterior is substituted. -/
theorem p4Q2PZ37ACB_centeredCrossPartMass_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    mass b hb fH e (Γ e z) s = mass b hb fH e z (-s) := by
  unfold p4Q2PZ37ABY_originalCrossPartMass
  simp_rw [p4Q2PZ37ACB_centeredCrossPair_centerGauge]
  exact p4Q2PZ37ACB_pairHaar_central_integral
    (fun w : G × G => max (psi b hb fH e z (-s) w) 0)
    ((p4Q2PZ37ABY_originalCrossPair_continuous H b hb fH e z (-s)).max continuous_const)

/-- A genuine ABX-positive link cannot have strict fixed-orientation tail
dominance at EVERY outer context. The coefficient need only satisfy theta<1. -/
theorem p4Q2PZ37ACB_centeredRectangle_no_allContext_tailDominance
    (b : ℝ) (hb : 0 ≤ b) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb fH e)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (theta : ℝ) (htheta : theta < 1) :
    ¬ (∀ z : Cfg × Cfg, mass b hb fH e z (-s) ≤ theta * mass b hb fH e z s) := by
  intro hCap
  have hZero (z : Cfg × Cfg) :
      mass b hb fH e z s = 0 ∧ mass b hb fH e z (-s) = 0 := by
    have hForward := hCap z
    have hReverse := hCap (Γ e z)
    simp only [p4Q2PZ37ACB_centeredCrossPartMass_centerGauge, neg_neg] at hReverse
    have hPos : 0 ≤ mass b hb fH e z s := integral_nonneg (fun _ => le_max_right _ _)
    have hNeg : 0 ≤ mass b hb fH e z (-s) := integral_nonneg (fun _ => le_max_right _ _)
    have hSum : mass b hb fH e z s + mass b hb fH e z (-s) ≤ 0 := by
      by_contra hn
      have hp := mul_pos (sub_pos.mpr htheta) (lt_of_not_ge hn)
      nlinarith [hForward, hReverse, hp]
    constructor <;> apply le_antisymm <;> linarith
  have hPositive : 0 < mass b hb fH e R.anchor R.sign :=
    (mul_pos (mul_pos R.eta_pos R.kappa_pos) R.inner_mass_pos).trans_le
      (p4Q2PZ37ABY_rectangle_crossPositive_mass_lower H b hb fH e R R.anchor R.anchor_mem)
  have hSigns : R.sign = s ∨ R.sign = -s := by
    rcases R.orientation with hR | hR <;> rcases hs with hS | hS <;> simp [hR, hS]
  obtain ⟨hP, hN⟩ := hZero R.anchor
  rcases hSigns with hSigns | hSigns
  · rw [hSigns, hP] at hPositive
    linarith
  · rw [hSigns, hN] at hPositive
    linarith

/-- Unconditionally at every finite H,b>0, SOME actual active link has
no strict all-context tail-dominance ratio for either fixed orientation.
This does not quantify over every link and does not rule out selected events. -/
theorem p4Q2PZ37ACB_exists_activeLink_no_allContext_tailDominance
    (b : ℝ) (hb : 0 < b) :
    ∃ e : Link, ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ theta : ℝ, theta < 1 →
      ¬ (∀ z : Cfg × Cfg,
        mass b hb.le fH e z (-s) ≤ theta * mass b hb.le fH e z s) := by
  obtain ⟨e, ⟨R⟩⟩ := p4Q2PZ37ABX_exists_centeredPhysical_alignmentRectangle H b hb
  exact ⟨e, fun s hs theta htheta =>
    p4Q2PZ37ACB_centeredRectangle_no_allContext_tailDominance H b hb.le e R s hs theta htheta⟩

/-- On an original active link, EACH fixed orientation has a boundary
context with strictly positive full mismatch for the SAME centered source. -/
theorem p4Q2PZ37ACB_exists_activeLink_positiveMismatch_eachOrientation
    (b : ℝ) (hb : 0 < b) :
    ∃ e : Link, ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ∃ z : Cfg × Cfg, 0 < mass b hb.le fH e z (-s) := by
  obtain ⟨e, he⟩ := p4Q2PZ37ACB_exists_activeLink_no_allContext_tailDominance H b hb
  refine ⟨e, ?_⟩
  intro s hs
  have hn := he s hs 0 (by norm_num)
  by_contra hNone
  apply hn
  intro z
  have hz : mass b hb.le fH e z (-s) ≤ 0 :=
    le_of_not_gt (fun hpos => hNone ⟨z, hpos⟩)
  simpa only [zero_mul] using hz

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredReceiver_covariance_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredReceiver_variance_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredTransfer_covariance_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredTransfer_variance_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredReceiver_defect_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredTransfer_defect_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredOptimizedBudget_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredCrossPair_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredCrossPartMass_centerGauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_centeredRectangle_no_allContext_tailDominance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_exists_activeLink_no_allContext_tailDominance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_exists_activeLink_positiveMismatch_eachOrientation
