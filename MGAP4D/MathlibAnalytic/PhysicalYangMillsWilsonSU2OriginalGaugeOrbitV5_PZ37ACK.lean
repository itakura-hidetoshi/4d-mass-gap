import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeMismatchObstructionV5_PZ37ACC

/-!
# P4-Q2-PZ37ACK — genuine SU(2) gauge orbit of the original receiver

Place an arbitrary element of the ORIGINAL SU(2) at the source vertex of
the chosen link, and apply this same lattice gauge transformation to both
outer boundaries. The original physical source, genuine Perron factors,
and joint half-density obey their already proved gauge invariance.

The literal link replacement therefore gives
  F_(Gamma_a z)(g) = F_z(a^(-1)*g).
This genuine gauge action preserves original outer pair Haar, link means,
and link variances. Its energy covariance is exactly the translated
fundamental-character moment of the SAME receiver. The action is jointly
continuous in its SU(2) value and its original outer context.

The identity and center actions agree with the original definitions. In
particular, ACC's center covariance sign reversal and even regression
defect remain unchanged. No posterior anchor is transported here, and no
GI-gap sign law, residual-smallness assumption, or coercivity is asserted.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACK_orbitGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACK_orbitCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACK_orbitCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACK_orbitMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACK_orbitBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACK_orbitProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

private theorem p4Q2PZ37ACK_covariance_eq_character
    (Q : G → ℝ) (hQ : Continuous Q) :
    Cov Q E = -(∫ g : G, Q g * χ g ∂μ) := by
  have hQI : Integrable Q μ :=
    hQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQE : Integrable (fun g : G => Q g * E g) μ :=
    (hQ.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMoment : (∫ g : G, Q g * χ g ∂μ) =
      (∫ g : G, Q g ∂μ) - ∫ g : G, Q g * E g ∂μ := by
    calc
      _ = ∫ g : G, Q g - Q g * E g ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        unfold p4Q2PZ35C_originalOneLinkCharacter
        ring
      _ = _ := integral_sub hQI hQE
  unfold CompactEnergyMismatchMoment.covariance
  rw [p4Q2PZ37ABZ_originalEnergy_Haar_mean, mul_one, hMoment]
  ring

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Vertex" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "GT" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "GA" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "sqrtD" => continuousJointSqrtDensity H 2 (by norm_num)
local notation "I" => decomposableOneSliceTransferIntegral H 2
local notation "fH" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local instance p4Q2PZ37ACK_orbitLinks : Fintype Link := Fintype.ofFinite _

/-- The actual source-vertex gauge takes any value in the original SU(2). -/
def p4Q2PZ37ACK_originalGauge (e : Link) (a : G) : GT :=
  Function.update (fun _ : Vertex => (1 : G)) e.1 a

/-- The SAME actual gauge transformation acts on both outer boundaries. -/
def p4Q2PZ37ACK_originalGaugePair (e : Link) (a : G) (z : Cfg × Cfg) : Cfg × Cfg :=
  (GA (p4Q2PZ37ACK_originalGauge H e a) z.1,
    GA (p4Q2PZ37ACK_originalGauge H e a) z.2)
local notation "gamma" => p4Q2PZ37ACK_originalGauge H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H

/-- The identity element gives the unchanged original context. -/
theorem p4Q2PZ37ACK_originalGaugePair_one (e : Link) (z : Cfg × Cfg) :
    Γ e (1 : G) z = z := by
  have hGamma : gamma e (1 : G) = (1 : GT) := by
    funext v
    by_cases hv : v = e.1
    · subst v
      simp [p4Q2PZ37ACK_originalGauge]
    · simp [p4Q2PZ37ACK_originalGauge, hv]
  unfold p4Q2PZ37ACK_originalGaugePair
  rw [hGamma]
  simp only [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_one]

/-- At the genuine central minus identity this is exactly ACC's action. -/
theorem p4Q2PZ37ACK_originalGaugePair_center (e : Link) (z : Cfg × Cfg) :
    Γ e p4Q2PZ35D4_centralMinusOne z =
      p4Q2PZ37ACC_originalCenterGaugePair H e z := rfl

/-- Every member of the genuine gauge orbit preserves ORIGINAL outer Haar. -/
theorem p4Q2PZ37ACK_originalGaugePair_measurePreserving (e : Link) (a : G) :
    MeasurePreserving (Γ e a) outer outer := by
  change MeasurePreserving
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairGaugeTransform H 2 (gamma e a))
    outer outer
  exact periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving
    H 2 (gamma e a)

private theorem p4Q2PZ37ACK_originalGauge_eval_continuous (e : Link) (v : Vertex) :
    Continuous (fun a : G => gamma e a v) := by
  by_cases hv : v = e.1
  · subst v
    simpa only [p4Q2PZ37ACK_originalGauge, Function.update_self] using
      (continuous_id : Continuous (fun a : G => a))
  · simpa only [p4Q2PZ37ACK_originalGauge, Function.update_of_ne hv] using
      (continuous_const : Continuous (fun _a : G => (1 : G)))

/-- Joint continuity of the genuine SU(2) value and both original contexts. -/
theorem p4Q2PZ37ACK_originalGaugePair_continuous (e : Link) :
    Continuous (fun w : G × (Cfg × Cfg) => Γ e w.1 w.2) := by
  -- Expose the pair and each link coordinate before elaborating continuity.
  -- Keep definitional-equality elaboration at group-valued coordinates rather
  -- than composing configuration-valued theorems against a hidden pair action.
  unfold p4Q2PZ37ACK_originalGaugePair
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
  apply Continuous.prodMk
  · apply continuous_pi
    intro k
    have hSource : Continuous (fun w : G × (Cfg × Cfg) => gamma e w.1 k.1) :=
      (p4Q2PZ37ACK_originalGauge_eval_continuous H e k.1).comp
        (show Continuous (fun w : G × (Cfg × Cfg) => w.1) from continuous_fst)
    have hLink : Continuous (fun w : G × (Cfg × Cfg) => w.2.1 k) :=
      (show Continuous (fun B : Cfg => B k) from continuous_apply k).comp
        (show Continuous (fun w : G × (Cfg × Cfg) => w.2.1) from
          continuous_fst.comp continuous_snd)
    have hTarget : Continuous (fun w : G × (Cfg × Cfg) =>
        (gamma e w.1 (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹) :=
      ((p4Q2PZ37ACK_originalGauge_eval_continuous H e
        (periodicHypercubicEvenSpatialSliceShift H k.1 k.2)).comp
          (show Continuous (fun w : G × (Cfg × Cfg) => w.1) from continuous_fst)).inv
    exact (hSource.mul hLink).mul hTarget
  · apply continuous_pi
    intro k
    have hSource : Continuous (fun w : G × (Cfg × Cfg) => gamma e w.1 k.1) :=
      (p4Q2PZ37ACK_originalGauge_eval_continuous H e k.1).comp
        (show Continuous (fun w : G × (Cfg × Cfg) => w.1) from continuous_fst)
    have hLink : Continuous (fun w : G × (Cfg × Cfg) => w.2.2 k) :=
      (show Continuous (fun B : Cfg => B k) from continuous_apply k).comp
        (show Continuous (fun w : G × (Cfg × Cfg) => w.2.2) from
          continuous_snd.comp continuous_snd)
    have hTarget : Continuous (fun w : G × (Cfg × Cfg) =>
        (gamma e w.1 (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹) :=
      ((p4Q2PZ37ACK_originalGauge_eval_continuous H e
        (periodicHypercubicEvenSpatialSliceShift H k.1 k.2)).comp
          (show Continuous (fun w : G × (Cfg × Cfg) => w.1) from continuous_fst)).inv
    exact (hSource.mul hLink).mul hTarget

/-- Continuity along a genuine gauge orbit with the outer context fixed. -/
theorem p4Q2PZ37ACK_originalGaugePair_continuous_a (e : Link) (z : Cfg × Cfg) :
    Continuous (fun a : G => Γ e a z) := by
  unfold p4Q2PZ37ACK_originalGaugePair
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
  apply Continuous.prodMk
  · apply continuous_pi
    intro k
    have hSource : Continuous (fun a : G => gamma e a k.1) :=
      p4Q2PZ37ACK_originalGauge_eval_continuous H e k.1
    have hLink : Continuous (fun _a : G => z.1 k) := continuous_const
    have hTarget : Continuous (fun a : G =>
        (gamma e a (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹) :=
      (p4Q2PZ37ACK_originalGauge_eval_continuous H e
        (periodicHypercubicEvenSpatialSliceShift H k.1 k.2)).inv
    exact (hSource.mul hLink).mul hTarget
  · apply continuous_pi
    intro k
    have hSource : Continuous (fun a : G => gamma e a k.1) :=
      p4Q2PZ37ACK_originalGauge_eval_continuous H e k.1
    have hLink : Continuous (fun _a : G => z.2 k) := continuous_const
    have hTarget : Continuous (fun a : G =>
        (gamma e a (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹) :=
      (p4Q2PZ37ACK_originalGauge_eval_continuous H e
        (periodicHypercubicEvenSpatialSliceShift H k.1 k.2)).inv
    exact (hSource.mul hLink).mul hTarget

/-- Continuity in the original outer context for each fixed gauge value. -/
theorem p4Q2PZ37ACK_originalGaugePair_continuous_z (e : Link) (a : G) :
    Continuous (Γ e a) := by
  unfold p4Q2PZ37ACK_originalGaugePair
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
  apply Continuous.prodMk
  · apply continuous_pi
    intro k
    have hSource : Continuous (fun _z : Cfg × Cfg => gamma e a k.1) := continuous_const
    have hLink : Continuous (fun z : Cfg × Cfg => z.1 k) :=
      (show Continuous (fun B : Cfg => B k) from continuous_apply k).comp
        (show Continuous (fun z : Cfg × Cfg => z.1) from continuous_fst)
    have hTarget : Continuous (fun _z : Cfg × Cfg =>
        (gamma e a (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹) := continuous_const
    exact (hSource.mul hLink).mul hTarget
  · apply continuous_pi
    intro k
    have hSource : Continuous (fun _z : Cfg × Cfg => gamma e a k.1) := continuous_const
    have hLink : Continuous (fun z : Cfg × Cfg => z.2 k) :=
      (show Continuous (fun B : Cfg => B k) from continuous_apply k).comp
        (show Continuous (fun z : Cfg × Cfg => z.2) from continuous_snd)
    have hTarget : Continuous (fun _z : Cfg × Cfg =>
        (gamma e a (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹) := continuous_const
    exact (hSource.mul hLink).mul hTarget

private theorem p4Q2PZ37ACK_gauge_update
    (delta : GT) (B : Cfg) (e : Link) (g : G) :
    GA delta (Function.update B e g) =
      Function.update (GA delta B) e
        (delta e.1 * g * (delta (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹) := by
  funext k
  change delta k.1 * (Function.update B e g) k *
      (delta (periodicHypercubicEvenSpatialSliceShift H k.1 k.2))⁻¹ = _
  by_cases hk : k = e
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hk]
    rfl

/-- Literal right-link replacement commutes with the actual source gauge.
The two lattice endpoints are distinct at every original H, including zero. -/
theorem p4Q2PZ37ACK_originalGauge_update (e : Link) (a : G) (B : Cfg) (g : G) :
    GA (gamma e a) (Function.update B e g) =
      Function.update (GA (gamma e a) B) e (a * g) := by
  have hSource : gamma e a e.1 = a := by
    simp [p4Q2PZ37ACK_originalGauge]
  have hTarget : gamma e a (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [p4Q2PZ37ACK_originalGauge,
      p4Q2LK_originalSpatialLink_target_ne_source H e]
  rw [p4Q2PZ37ACK_gauge_update H (gamma e a) B e g, hSource, hTarget]
  simp only [inv_one, mul_one]

/-- The true transfer/Perron prefactor is invariant under this same gauge. -/
theorem p4Q2PZ37ACK_originalPrefactor_gauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) :
    P b hb (Γ e a z) = P b hb z := by
  unfold p4Q2PZ37ABZ_originalTransferSectionPrefactor
  exact congrArg (fun x : ℝ =>
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * x)
    (p4Q2PZ37ACC_originalJointSqrtDensity_gaugeInvariant H b hb (gamma e a) z)

private theorem p4Q2PZ37ACK_centeredTransferSection_equivariant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) (g : G) :
    U b hb fH e (Γ e a z) (a * g) = U b hb fH e z g := by
  change
    I b fH (Function.update (GA (gamma e a) z.2) e (a * g)) /
        sqrtD b hb (GA (gamma e a) z.1, Function.update (GA (gamma e a) z.2) e (a * g)) =
      I b fH (Function.update z.2 e g) / sqrtD b hb (z.1, Function.update z.2 e g)
  rw [← p4Q2PZ37ACK_originalGauge_update H e a z.2 g,
    p4Q2PZ37ACC_centeredPhysicalTransfer_gaugeInvariant
      H b (gamma e a) (Function.update z.2 e g),
    p4Q2PZ37ACC_originalJointSqrtDensity_gaugeInvariant
      H b hb (gamma e a) (z.1, Function.update z.2 e g)]

/-- Exact SU(2) transport of the original centered transfer section. -/
theorem p4Q2PZ37ACK_centeredTransferSection_gauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) (g : G) :
    U b hb fH e (Γ e a z) g = U b hb fH e z (a⁻¹ * g) := by
  have h := p4Q2PZ37ACK_centeredTransferSection_equivariant H b hb e a z (a⁻¹ * g)
  have hMul : a * (a⁻¹ * g) = g := by group
  rw [hMul] at h
  exact h

/-- The SAME original centered-source FF receiver along its actual gauge orbit. -/
theorem p4Q2PZ37ACK_centeredReceiver_gauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) (g : G) :
    F b hb fH e (Γ e a z) g = F b hb fH e z (a⁻¹ * g) := by
  unfold p4Q2PZ37ABZ_originalReceiverSection
  rw [p4Q2PZ37ABZ_originalResponse_eq_transferSection,
    p4Q2PZ37ABZ_originalResponse_eq_transferSection,
    p4Q2PZ37ACK_originalPrefactor_gauge H b hb e a z,
    p4Q2PZ37ACK_centeredTransferSection_gauge H b hb e a z g]
  have hI := p4Q2PZ37ACC_centeredPhysicalTransfer_gaugeInvariant H b (gamma e a) z.2
  change I b fH (Γ e a z).2 = I b fH z.2 at hI
  rw [hI]

/-- Link continuity of the unchanged original receiver. -/
theorem p4Q2PZ37ACK_centeredReceiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb fH e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b hb fH e).continuous.comp
      (continuous_const.prodMk continuous_id)

/-- Gauge transport preserves the genuine single-link Haar mean. -/
theorem p4Q2PZ37ACK_centeredReceiver_mean_gauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) :
    (∫ g : G, F b hb fH e (Γ e a z) g ∂μ) = ∫ g : G, F b hb fH e z g ∂μ := by
  simp_rw [p4Q2PZ37ACK_centeredReceiver_gauge H b hb e a z]
  exact p4Q2PZ35C_originalSU2Haar_integral_left_translate
    (F b hb fH e z) (p4Q2PZ37ACK_centeredReceiver_continuous H b hb e z) a⁻¹

/-- The original receiver variance is constant on the full genuine SU(2) orbit. -/
theorem p4Q2PZ37ACK_centeredReceiver_variance_gauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) :
    Var (F b hb fH e (Γ e a z)) = Var (F b hb fH e z) := by
  have hF := p4Q2PZ37ACK_centeredReceiver_continuous H b hb e z
  have hSquare :
      (∫ g : G, F b hb fH e (Γ e a z) g * F b hb fH e (Γ e a z) g ∂μ) =
        ∫ g : G, F b hb fH e z g * F b hb fH e z g ∂μ := by
    simp_rw [p4Q2PZ37ACK_centeredReceiver_gauge H b hb e a z]
    exact p4Q2PZ35C_originalSU2Haar_integral_left_translate
      (fun g : G => F b hb fH e z g * F b hb fH e z g) (hF.mul hF) a⁻¹
  unfold CompactEnergyMismatchMoment.variance CompactEnergyMismatchMoment.covariance
  rw [hSquare, p4Q2PZ37ACK_centeredReceiver_mean_gauge H b hb e a z]

/-- The actual energy covariance along the genuine gauge orbit is precisely
the translated fundamental-character moment of the SAME original receiver. -/
theorem p4Q2PZ37ACK_centeredReceiver_covariance_gauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (a : G) (z : Cfg × Cfg) :
    Cov (F b hb fH e (Γ e a z)) E =
      -(∫ g : G, F b hb fH e z g * χ (a * g) ∂μ) := by
  have hF := p4Q2PZ37ACK_centeredReceiver_continuous H b hb e (Γ e a z)
  have hChi : Continuous χ :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  rw [p4Q2PZ37ACK_covariance_eq_character (F b hb fH e (Γ e a z)) hF]
  congr 1
  calc
    (∫ g : G, F b hb fH e (Γ e a z) g * χ g ∂μ) =
        ∫ g : G, F b hb fH e (Γ e a z) (a * g) * χ (a * g) ∂μ :=
      (p4Q2PZ35C_originalSU2Haar_integral_left_translate
        (fun g : G => F b hb fH e (Γ e a z) g * χ g) (hF.mul hChi) a).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with g
      rw [p4Q2PZ37ACK_centeredReceiver_gauge H b hb e a z (a * g)]
      have hMul : a⁻¹ * (a * g) = g := by group
      rw [hMul]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGaugePair_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGaugePair_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGaugePair_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGaugePair_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGaugePair_continuous_a
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGaugePair_continuous_z
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalGauge_update
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_originalPrefactor_gauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_centeredTransferSection_gauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_centeredReceiver_gauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_centeredReceiver_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_centeredReceiver_mean_gauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_centeredReceiver_variance_gauge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACK_centeredReceiver_covariance_gauge
