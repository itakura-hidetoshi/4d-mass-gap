import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorEnergyRegressionV5_PZ37ACH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeMismatchObstructionV5_PZ37ACC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonContinuousPhysicalGIDetectionV5_OT

/-!
# P4-Q2-PZ37ACI — nonzero energy covariance of the original physical source

For the SAME original FF receiver F and genuine Haar energy E, prove
  Cov(F,E) = integral JQ_receiver(g) (1-E(g)) dHaar(g) / q(z),
where q(z)>0 is the original Perron/transfer density-cancellation weight.
LC's exact left-boundary factorization and LA's proved negative-exponential
Haar injectivity detect this actual energy moment whenever the original
physical transfer is nonzero on the identity right-link fiber.

OT supplies that nonzero original transfer fiber for every chosen spatial
link of any nonzero physical source with a continuous gauge-invariant
representative. The ORIGINAL centered Gauss-law source has exactly such
a representative by AAU and is nonzero by ZW. Consequently, at every
finite H and b>0, EVERY actual link has a genuine boundary context with
nonzero Cov(F,E). ACC's actual center-gauge transport then gives both signs.

The continuous Haar test used inside the injectivity argument is a rewrite
of the true receiver, not a new physical source or a replacement posterior.
All transfer norms, the genuine Perron representative, and both interacting
posterior laws remain unchanged. This proves qualitative finite-volume
covariance nondegeneracy. It gives neither a numerical H-uniform covariance
floor nor small regression defect, GI-moment coercivity or continuum mass gap.
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
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local instance p4Q2PZ37ACI_covarianceGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACI_covarianceCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACI_covarianceCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACI_covarianceMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACI_covarianceBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACI_covarianceProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

private theorem p4Q2PZ37ACI_character_continuous : Continuous χ := by
  change Continuous (fun g : G => (1 : ℝ) - E g)
  exact continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

private theorem p4Q2PZ37ACI_character_identity : χ (1 : G) = 1 := by
  unfold p4Q2PZ35C_originalOneLinkCharacter
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  norm_num

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "GT" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "GA" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "J" => p4Q2JQ_originalPhysicalSourceLinkReceiver H
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local instance p4Q2PZ37ACI_covarianceLinks : Fintype Link := Fintype.ofFinite _

private theorem p4Q2PZ37ACI_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b hb f e).continuous.comp
      (continuous_const.prodMk continuous_id)

/-- Exact covariance of the unchanged FF receiver. The spatial Haar centering
of the physical source is not confused with centering on this link section. -/
theorem p4Q2PZ37ACI_originalEnergyCovariance_eq_receiverCharacter
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Cov (F b hb f e z) E =
      (∫ g : G, J b hb f e z g * χ g ∂μ) / q b hb z := by
  let R : C(G, ℝ) := J b hb f e z
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF
    H 2 (by norm_num) b hb f
  have hR : Integrable (fun g : G => R g) μ :=
    R.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRE : Integrable (fun g : G => R g * E g) μ :=
    (R.continuous.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMoment : (∫ g : G, R g * χ g ∂μ) =
      (∫ g : G, R g ∂μ) - ∫ g : G, R g * E g ∂μ := by
    calc
      _ = ∫ g : G, R g - R g * E g ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        unfold p4Q2PZ35C_originalOneLinkCharacter
        ring
      _ = _ := integral_sub hR hRE
  have hCovR : Cov (fun g : G => R g) E = -(∫ g : G, R g * χ g ∂μ) := by
    unfold CompactEnergyMismatchMoment.covariance
    rw [p4Q2PZ37ABZ_originalEnergy_Haar_mean, mul_one, hMoment]
    ring
  have hDiff (g h : G) : F b hb f e z g - F b hb f e z h =
      (-(q b hb z)⁻¹) * (R g - R h) := by
    unfold p4Q2PZ37ABZ_originalReceiverSection
    rw [p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_apply,
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_apply]
    change (O z - R g) / q b hb z - (O z - R h) / q b hb z =
      (-(q b hb z)⁻¹) * (R g - R h)
    ring
  have hCov := CompactEnergyMismatchMoment.covariance_of_difference_eq μ
    (F b hb f e z) (fun g : G => R g) E (-(q b hb z)⁻¹)
    (p4Q2PZ37ACI_receiver_continuous H b hb f e z) R.continuous
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) hDiff
  rw [hCovR] at hCov
  calc
    Cov (F b hb f e z) E =
        (-(q b hb z)⁻¹) * (-(∫ g : G, R g * χ g ∂μ)) := hCov
    _ = (∫ g : G, J b hb f e z g * χ g ∂μ) / q b hb z := by
      change (-(q b hb z)⁻¹) * (-(∫ g : G, R g * χ g ∂μ)) =
        (∫ g : G, R g * χ g ∂μ) / q b hb z
      ring

/-- Auxiliary analytic test formed from the actual receiver and actual energy.
It is not used as a replacement physical source or posterior density. -/
private def p4Q2PZ37ACI_energyCompensatedRightSource
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (u₀ : G) : C(G, ℝ) := by
  let R₀ : C(G, ℝ) := J b hb f e (Function.update left₀ e u₀, right)
  have hExp : Continuous (fun g : G =>
      Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))) := by
    have hE : Continuous (fun g : G =>
        p4Q2KR_originalSU2FeatureExponentialContinuous (b / 4) (u₀, g)) :=
      (p4Q2KR_originalSU2FeatureExponentialContinuous (b / 4)).continuous.comp
        (continuous_const.prodMk continuous_id)
    simpa only [p4Q2KR_originalSU2FeatureExponentialContinuous_apply] using hE
  exact ⟨fun g => R₀ g * χ g * Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)),
    (R₀.continuous.mul p4Q2PZ37ACI_character_continuous).mul hExp⟩

private theorem p4Q2PZ37ACI_energyCompensatedRightSource_apply
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (u₀ g : G) :
    p4Q2PZ37ACI_energyCompensatedRightSource H b hb f left₀ right e u₀ g =
      J b hb f e (Function.update left₀ e u₀, right) g * χ g *
        Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) := rfl

private theorem p4Q2PZ37ACI_energyCompensatedRightSource_ne_zero
    (b : ℝ) (hb : 0 < b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (u₀ : G)
    (ht : decomposableOneSliceTransferIntegral H 2 b f
      (Function.update right e (1 : G)) ≠ 0) :
    p4Q2PZ37ACI_energyCompensatedRightSource H b hb.le f left₀ right e u₀ ≠ 0 := by
  have hL :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb.le‖⁻¹ ≠ 0 :=
    inv_ne_zero (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b hb.le).ne'
  have hs : continuousJointSqrtDensity H 2 (by norm_num) b hb.le
      (Function.update left₀ e u₀, Function.update right e (1 : G)) ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb.le
      (Function.update left₀ e u₀, Function.update right e (1 : G))).ne'
  have hJ : J b hb.le f e (Function.update left₀ e u₀, right) (1 : G) ≠ 0 := by
    rw [p4Q2JQ_originalPhysicalSourceLinkReceiver_apply,
      p4Q2GN_originalReceiver_eq_transferIntegral]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hL) ht) hs
  have hValue :
      p4Q2PZ37ACI_energyCompensatedRightSource
        H b hb.le f left₀ right e u₀ (1 : G) ≠ 0 := by
    rw [p4Q2PZ37ACI_energyCompensatedRightSource_apply,
      p4Q2PZ37ACI_character_identity, mul_one]
    exact mul_ne_zero hJ (Real.exp_pos _).ne'
  intro hZero
  apply hValue
  rw [hZero]
  simp

private theorem p4Q2PZ37ACI_receiverEnergyTest_factorization
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (h u₀ u : G) :
    (∫ g : G, J b hb f e (Function.update left₀ e u, right) g * χ g ∂μ) =
      (p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u /
        p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u₀) *
      (∫ g : G, Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) *
        p4Q2PZ37ACI_energyCompensatedRightSource H b hb f left₀ right e u₀ g ∂μ) := by
  let R : G → C(G, ℝ) := fun v => J b hb f e (Function.update left₀ e v, right)
  let C : G → ℝ := p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h
  let A : G → ℝ := p4Q2KZ_originalRightLinkScale H b hb left₀ right e
  let N : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb‖⁻¹ ^ 2
  let M : G → ℝ := fun g => decomposableOneSliceTransferIntegral
    H 2 b f (Function.update right e g)
  let X : G → G → ℝ := fun v g => Real.exp (-(b / 4) * inner ℝ (Phi v) (Phi g))
  let ψ : C(G, ℝ) := p4Q2PZ37ACI_energyCompensatedRightSource
    H b hb f left₀ right e u₀
  have hC₀ : C u₀ ≠ 0 :=
    (p4Q2KZ_originalLeftBoundaryScale_pos H b hb left₀ right e h u₀).ne'
  have hR (v g : G) : R v g = N * M g * (C v * A g * X v g) :=
    p4Q2LC_originalPhysicalSourceReceiver_leftBoundary_factorization
      H b hb f left₀ right e h v g
  have hXcancel (g : G) : X u₀ g *
      Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) = 1 := by
    dsimp [X]
    rw [← Real.exp_add]
    have hArg : -(b / 4) * inner ℝ (Phi u₀) (Phi g) +
        (b / 4) * inner ℝ (Phi u₀) (Phi g) = 0 := by ring
    rw [hArg, Real.exp_zero]
  have hReference (g : G) :
      R u₀ g * Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) =
        N * M g * (C u₀ * A g) := by
    rw [hR u₀ g]
    calc
      N * M g * (C u₀ * A g * X u₀ g) *
          Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) =
        (N * M g * (C u₀ * A g)) *
          (X u₀ g * Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))) := by ring
      _ = N * M g * (C u₀ * A g) := by rw [hXcancel g]; ring
  have hPoint (g : G) : R u g * χ g = (C u / C u₀) * (X u g * ψ g) := by
    rw [p4Q2PZ37ACI_energyCompensatedRightSource_apply]
    change R u g * χ g = (C u / C u₀) *
      (X u g * ((R u₀ g * χ g) * Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))))
    calc
      R u g * χ g = (N * M g * (C u * A g * X u g)) * χ g := by rw [hR]
      _ = (C u / C u₀) * (X u g * ((N * M g * (C u₀ * A g)) * χ g)) := by
        field_simp [hC₀]
      _ = (C u / C u₀) *
          (X u g * ((R u₀ g * Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))) * χ g)) := by
        rw [hReference]
      _ = _ := by ring
  change (∫ g : G, R u g * χ g ∂μ) = (C u / C u₀) * (∫ g : G, X u g * ψ g ∂μ)
  calc
    _ = ∫ g : G, (C u / C u₀) * (X u g * ψ g) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      exact hPoint g
    _ = _ := integral_const_mul _ _

/-- The actual energy covariance is detected by an authentic left boundary
whenever the same physical transfer is nonzero on the identity right fiber.
The centered-source theorem below proves this transfer premise. -/
theorem p4Q2PZ37ACI_originalEnergyCovariance_nonzero_some_left_of_transfer_identity
    (b : ℝ) (hb : 0 < b) (f : Phys)
    (left₀ right : Cfg) (e : Link)
    (ht : decomposableOneSliceTransferIntegral H 2 b f
      (Function.update right e (1 : G)) ≠ 0) :
    ∃ u : G, Cov (F b hb.le f e (Function.update left₀ e u, right)) E ≠ 0 := by
  let ψ : C(G, ℝ) := p4Q2PZ37ACI_energyCompensatedRightSource
    H b hb.le f left₀ right e (1 : G)
  have hψ : ψ ≠ 0 := p4Q2PZ37ACI_energyCompensatedRightSource_ne_zero
    H b hb f left₀ right e (1 : G) ht
  obtain ⟨u, hu⟩ := p4Q2LA_originalNegativeExponentialHaarTransform_exists_nonzero_receiver
    b hb ψ hψ
  have hScale : 0 <
      p4Q2KZ_originalLeftBoundaryScale H b hb.le left₀ right e (1 : G) u /
        p4Q2KZ_originalLeftBoundaryScale H b hb.le left₀ right e (1 : G) (1 : G) :=
    div_pos
      (p4Q2KZ_originalLeftBoundaryScale_pos H b hb.le left₀ right e (1 : G) u)
      (p4Q2KZ_originalLeftBoundaryScale_pos H b hb.le left₀ right e (1 : G) (1 : G))
  refine ⟨u, ?_⟩
  rw [p4Q2PZ37ACI_originalEnergyCovariance_eq_receiverCharacter]
  apply div_ne_zero ?_
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos H b hb.le (Function.update left₀ e u, right)).ne'
  rw [p4Q2PZ37ACI_receiverEnergyTest_factorization H b hb.le f left₀ right e (1 : G) (1 : G) u]
  exact mul_ne_zero hScale.ne' hu

/-- Genuine full Wilson transfer positivity discharges the nonzero transfer
condition for every chosen link of a nonzero continuous physical source. -/
theorem p4Q2PZ37ACI_originalPhysicalEnergyCovariance_nonzero
    (b : ℝ) (hb : 0 < b) (f : Phys) (hf : f ≠ 0)
    (hRegular : p4Q2OT_hasGaugeContinuousRepresentative H f)
    (e : Link) (left₀ : Cfg) :
    ∃ z : Cfg × Cfg, Cov (F b hb.le f e z) E ≠ 0 := by
  obtain ⟨ψ, hRep, hGauge⟩ := hRegular
  have hψ : ψ ≠ 0 := p4Q2OT_originalContinuousRepresentative_ne_zero H f hf ψ hRep
  obtain ⟨right, hRight⟩ :=
    p4Q2OT_originalContinuousPhysical_transfer_nonzero_identityFiber
      H b hb f ψ hRep hψ hGauge e
  obtain ⟨u, hu⟩ :=
    p4Q2PZ37ACI_originalEnergyCovariance_nonzero_some_left_of_transfer_identity
      H b hb f left₀ right e hRight
  exact ⟨(Function.update left₀ e u, right), hu⟩

/-- Unconditional original-model covariance nondegeneracy for the SAME
centered Gauss-law source at every finite volume, positive coupling and link.
Neither a covariance premise nor a new physical source occurs. -/
theorem p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
    (b : ℝ) (hb : 0 < b) (e : Link) (left₀ : Cfg) :
    ∃ z : Cfg × Cfg, Cov (F b hb.le f₀ e z) E ≠ 0 := by
  let ψ : C(Cfg, ℝ) := p4Q2PZ37AAU_originalCenteredWilsonContinuous H
  have hRep : (fun A : Cfg => (f₀ : Lp ℝ 2 haar) A) =ᵐ[haar] ψ := by
    rw [p4Q2PZ37AAU_originalCenteredWilsonPhysical_eq_continuousLp H]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hGauge : ∀ gamma : GT, ∀ A : Cfg, ψ (GA gamma A) = ψ A :=
    fun gamma A => p4Q2OV_originalPhysicalContinuousRepresentative_gaugeInvariant
      H f₀ ψ hRep gamma A
  exact p4Q2PZ37ACI_originalPhysicalEnergyCovariance_nonzero
    H b hb f₀ (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)
    ⟨ψ, hRep, hGauge⟩ e left₀

/-- The genuine center-gauge orbit gives BOTH signs of the actual energy
covariance on every chosen link. It does not give a sign law for the GI gap. -/
theorem p4Q2PZ37ACI_centeredEnergyCovariance_both_signs
    (b : ℝ) (hb : 0 < b) (e : Link) (left₀ : Cfg) :
    ∃ zPos zNeg : Cfg × Cfg,
      0 < Cov (F b hb.le f₀ e zPos) E ∧ Cov (F b hb.le f₀ e zNeg) E < 0 := by
  obtain ⟨z, hz⟩ := p4Q2PZ37ACI_centeredEnergyCovariance_nonzero H b hb e left₀
  have hFlip := p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge H b hb.le e z
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · exact ⟨p4Q2PZ37ACC_originalCenterGaugePair H e z, z, by linarith, hneg⟩
  · exact ⟨z, p4Q2PZ37ACC_originalCenterGaugePair H e z, hpos, by linarith⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalEnergyCovariance_eq_receiverCharacter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalEnergyCovariance_nonzero_some_left_of_transfer_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalPhysicalEnergyCovariance_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_centeredEnergyCovariance_both_signs
