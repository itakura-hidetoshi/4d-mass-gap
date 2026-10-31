import MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoCenterPathV5_PZ37ACL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFourModeDecompositionV5_PZ37ACK
import Mathlib.Topology.Order.IntermediateValue

/-!
# P4-Q2-PZ37ACL — original zero-covariance positive-variance obstruction

At every finite H, positive coupling b and chosen genuine link e, ACI
supplies an actual original context with positive energy covariance.
The existing original SU(2) rotation path joins the identity to the SAME
central minus one. ACD and ACK give continuity of covariance along its
genuine gauge orbit, while ACC gives opposite endpoint signs. The
intermediate value theorem therefore gives an actual context with
zero covariance. ACK preserves its strictly positive receiver variance.

For the SAME original centered Gauss-law source and FF receiver, write
C(z)=Cov_Haar(F_z,E), V(z)=Var_Haar(F_z), D(z)=V(z)-4*C(z)^2.
At the constructed context, C=0 and D=V>0. Consequently, for EVERY finite
real K the strict failure set of D<=K*C^2 is open and has positive
ORIGINAL outer pair-Haar mass. No such cap holds everywhere or almost
everywhere. The same statements hold for D<=theta*V whenever theta<1.
The retained universal bound D<=V shows that the latter threshold is sharp.

These are finite-volume qualitative obstruction statements. The positive
event mass and positive local variance amplitude are not volume-uniform.
They do not exclude useful estimates on selected covariance regions.
No physical source, Perron representative, transfer norm, Wilson posterior,
outer law or earlier obstacle theorem is replaced. The GI positivity
threshold and the continuum mass gap remain unresolved.
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
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACL_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACL_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACL_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACL_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACL_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local notation "path" => p4Q2PZ37ACL_originalCenterPath
local instance p4Q2PZ37ACL_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACL_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The actual original centered receiver variance, with all factors retained. -/
def p4Q2PZ37ACL_originalCenteredReceiverVariance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  Var (F b hb f₀ e z)
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H

/-- The original energy-regression residual, not a replacement source. -/
def p4Q2PZ37ACL_originalCenteredRegressionDefect
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  V b hb e z - 4 * (C b hb e z) ^ 2
local notation "D" => p4Q2PZ37ACL_originalCenteredRegressionDefect H

private theorem p4Q2PZ37ACL_covariance_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (C b hb e) :=
  p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e

private theorem p4Q2PZ37ACL_variance_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (V b hb e) :=
  p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f₀ e

private theorem p4Q2PZ37ACL_four_covariance_sq_le_variance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    4 * (C b hb e z) ^ 2 ≤ V b hb e z :=
  CompactEnergyMismatchMoment.four_covariance_sq_le_variance μ
    (F b hb f₀ e z) E (p4Q2PZ37ACK_centeredReceiver_continuous H b hb e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    p4Q2PZ37ABZ_originalEnergy_Haar_variance

/-! Scope the original full-support instance to mass/AE proofs, as in ACD. -/
private theorem p4Q2PZ37ACL_outerOpenPos : Measure.IsOpenPosMeasure outer := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    infer_instance
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The actual path crosses zero covariance while preserving actual variance.
The positive starting covariance is discharged by ACI in the next theorem. -/
theorem p4Q2PZ37ACL_originalGaugePath_zeroCovariance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (hz : 0 < C b hb e z) :
    ∃ t ∈ Set.Icc (0 : ℝ) Real.pi,
      C b hb e (Γ e (path t) z) = 0 ∧
        V b hb e (Γ e (path t) z) = V b hb e z := by
  let h : ℝ → ℝ := fun t => C b hb e (Γ e (path t) z)
  have hOrbit : Continuous (fun a : G => C b hb e (Γ e a z)) :=
    (p4Q2PZ37ACL_covariance_continuous H b hb e).comp
      (p4Q2PZ37ACK_originalGaugePair_continuous_a H e z)
  have hCont : Continuous h := hOrbit.comp p4Q2PZ37ACL_originalCenterPath_continuous
  have hAtZero : h 0 = C b hb e z := by
    dsimp only [h]
    rw [p4Q2PZ37ACL_originalCenterPath_zero, p4Q2PZ37ACK_originalGaugePair_one]
  have hAtPi : h Real.pi = -C b hb e z := by
    dsimp only [h]
    rw [p4Q2PZ37ACL_originalCenterPath_pi, p4Q2PZ37ACK_originalGaugePair_center]
    exact p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge H b hb e z
  have hLeft : 0 < h 0 := by
    rw [hAtZero]
    exact hz
  have hRight : h Real.pi < 0 := by
    rw [hAtPi]
    exact neg_neg_of_pos hz
  have hZeroMem : (0 : ℝ) ∈ Set.Icc (h Real.pi) (h 0) := ⟨hRight.le, hLeft.le⟩
  obtain ⟨t, ht, htZero⟩ :=
    intermediate_value_Icc' Real.pi_pos.le hCont.continuousOn hZeroMem
  refine ⟨t, ht, htZero, ?_⟩
  exact p4Q2PZ37ACK_centeredReceiver_variance_gauge H b hb e (path t) z

/-- EVERY genuine link has an original zero-covariance context with positive
variance at every finite volume and positive coupling. No new witness is assumed. -/
theorem p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance
    (b : ℝ) (hb : 0 < b) (e : Link) :
    ∃ z : Pair, C b hb.le e z = 0 ∧ 0 < V b hb.le e z := by
  obtain ⟨z0, _zNeg, hz0, _hzNeg⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_both_signs
      H b hb e (originalWilsonExplicitIdentityBoundary H)
  have hC0 : 0 < C b hb.le e z0 := hz0
  have hV0 : 0 < V b hb.le e z0 :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) (pow_pos hC0 2)).trans_le
      (p4Q2PZ37ACL_four_covariance_sq_le_variance H b hb.le e z0)
  obtain ⟨t, _ht, hCt, hVt⟩ :=
    p4Q2PZ37ACL_originalGaugePath_zeroCovariance H b hb.le e z0 hC0
  refine ⟨Γ e (path t) z0, hCt, ?_⟩
  rw [hVt]
  exact hV0

/-- At an actual original context the full positive variance is residual. -/
theorem p4Q2PZ37ACL_exists_zeroCovariance_fullDefect
    (b : ℝ) (hb : 0 < b) (e : Link) :
    ∃ z : Pair, C b hb.le e z = 0 ∧ 0 < V b hb.le e z ∧
      D b hb.le e z = V b hb.le e z := by
  obtain ⟨z, hC, hV⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  exact ⟨z, hC, hV, by simp [p4Q2PZ37ACL_originalCenteredRegressionDefect, hC]⟩

/-- The original defect always lies between zero and the entire variance. -/
theorem p4Q2PZ37ACL_originalDefect_bounds
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    0 ≤ D b hb e z ∧ D b hb e z ≤ V b hb e z := by
  change 0 ≤ V b hb e z - 4 * (C b hb e z) ^ 2 ∧
    V b hb e z - 4 * (C b hb e z) ^ 2 ≤ V b hb e z
  exact ⟨sub_nonneg.mpr (p4Q2PZ37ACL_four_covariance_sq_le_variance H b hb e z),
    sub_le_self _ (mul_nonneg (by norm_num) (sq_nonneg _))⟩

/-- Strict failure of any finite covariance-square cap is genuinely open. -/
theorem p4Q2PZ37ACL_covarianceCapViolation_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (K : ℝ) :
    IsOpen {z : Pair | K * (C b hb e z) ^ 2 < D b hb e z} :=
  CompactZeroCovarianceResidualObstruction.strictViolation_isOpen
    (V b hb e) (C b hb e) (p4Q2PZ37ACL_variance_continuous H b hb e)
    (p4Q2PZ37ACL_covariance_continuous H b hb e) K

/-- EVERY finite covariance-square cap fails on positive original outer Haar mass. -/
theorem p4Q2PZ37ACL_covarianceCapViolation_mass_pos
    (b : ℝ) (hb : 0 < b) (e : Link) (K : ℝ) :
    0 < Measure.real outer {z : Pair | K * (C b hb.le e z) ^ 2 < D b hb.le e z} := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACL_outerOpenPos H
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  have hMass := CompactZeroCovarianceResidualObstruction.strictViolation_measure_pos
    outer (V b hb.le e) (C b hb.le e)
    (p4Q2PZ37ACL_variance_continuous H b hb.le e)
    (p4Q2PZ37ACL_covariance_continuous H b hb.le e) z0 hV0 hC0 K
  exact ENNReal.toReal_pos hMass.ne' (measure_ne_top _ _)

/-- One actual zero-covariance witness gives positive-mass violations for all
finite K while retaining half its strictly positive variance amplitude. -/
theorem p4Q2PZ37ACL_positiveVarianceViolation_mass_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    ∃ z0 : Pair, C b hb.le e z0 = 0 ∧ 0 < V b hb.le e z0 ∧
      ∀ K : ℝ, 0 < Measure.real outer {z : Pair |
        V b hb.le e z0 / 2 < V b hb.le e z ∧
          K * (C b hb.le e z) ^ 2 < D b hb.le e z} := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACL_outerOpenPos H
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  refine ⟨z0, hC0, hV0, ?_⟩
  intro K
  have hMass := CompactZeroCovarianceResidualObstruction.positiveAmplitudeViolation_measure_pos
    outer (V b hb.le e) (C b hb.le e)
    (p4Q2PZ37ACL_variance_continuous H b hb.le e)
    (p4Q2PZ37ACL_covariance_continuous H b hb.le e) z0 hV0 hC0 K
  exact ENNReal.toReal_pos hMass.ne' (measure_ne_top _ _)

/-- No finite covariance-square cap holds almost everywhere under original Haar. -/
theorem p4Q2PZ37ACL_no_ae_defect_covariance_cap
    (b : ℝ) (hb : 0 < b) (e : Link) (K : ℝ) :
    ¬ (∀ᵐ z ∂outer, D b hb.le e z ≤ K * (C b hb.le e z) ^ 2) := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACL_outerOpenPos H
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  exact CompactZeroCovarianceResidualObstruction.not_ae_cap
    outer (V b hb.le e) (C b hb.le e)
    (p4Q2PZ37ACL_variance_continuous H b hb.le e)
    (p4Q2PZ37ACL_covariance_continuous H b hb.le e) z0 hV0 hC0 K

/-- No finite covariance-square cap holds at every actual original context. -/
theorem p4Q2PZ37ACL_no_allContext_defect_covariance_cap
    (b : ℝ) (hb : 0 < b) (e : Link) (K : ℝ) :
    ¬ (∀ z : Pair, D b hb.le e z ≤ K * (C b hb.le e z) ^ 2) := by
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  exact CompactZeroCovarianceResidualObstruction.not_allContext_cap
    (V b hb.le e) (C b hb.le e) z0 hV0 hC0 K

/-- There is no finite real coefficient supplying an original-Haar AE cap. -/
theorem p4Q2PZ37ACL_no_exists_ae_defect_covariance_cap
    (b : ℝ) (hb : 0 < b) (e : Link) :
    ¬ (∃ K : ℝ, ∀ᵐ z ∂outer, D b hb.le e z ≤ K * (C b hb.le e z) ^ 2) := by
  rintro ⟨K, hCap⟩
  exact p4Q2PZ37ACL_no_ae_defect_covariance_cap H b hb e K hCap

/-- Strict failure of an original variance cap is open. -/
theorem p4Q2PZ37ACL_varianceCapViolation_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (theta : ℝ) :
    IsOpen {z : Pair | theta * V b hb e z < D b hb e z} :=
  CompactZeroCovarianceResidualObstruction.varianceStrictViolation_isOpen
    (V b hb e) (C b hb e) (p4Q2PZ37ACL_variance_continuous H b hb e)
    (p4Q2PZ37ACL_covariance_continuous H b hb e) theta

/-- Every variance cap below one fails on positive ORIGINAL outer Haar mass. -/
theorem p4Q2PZ37ACL_varianceCapViolation_mass_pos
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < 1) :
    0 < Measure.real outer {z : Pair | theta * V b hb.le e z < D b hb.le e z} := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACL_outerOpenPos H
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  have hMass := CompactZeroCovarianceResidualObstruction.varianceStrictViolation_measure_pos
    outer (V b hb.le e) (C b hb.le e)
    (p4Q2PZ37ACL_variance_continuous H b hb.le e)
    (p4Q2PZ37ACL_covariance_continuous H b hb.le e) z0 hV0 hC0 theta htheta
  exact ENNReal.toReal_pos hMass.ne' (measure_ne_top _ _)

/-- No coefficient below one is an almost-everywhere original variance cap. -/
theorem p4Q2PZ37ACL_no_ae_defect_variance_cap
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < 1) :
    ¬ (∀ᵐ z ∂outer, D b hb.le e z ≤ theta * V b hb.le e z) := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACL_outerOpenPos H
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  exact CompactZeroCovarianceResidualObstruction.not_ae_variance_cap
    outer (V b hb.le e) (C b hb.le e)
    (p4Q2PZ37ACL_variance_continuous H b hb.le e)
    (p4Q2PZ37ACL_covariance_continuous H b hb.le e) z0 hV0 hC0 theta htheta

/-- No coefficient below one caps the defect at every actual original context. -/
theorem p4Q2PZ37ACL_no_allContext_defect_variance_cap
    (b : ℝ) (hb : 0 < b) (e : Link) (theta : ℝ) (htheta : theta < 1) :
    ¬ (∀ z : Pair, D b hb.le e z ≤ theta * V b hb.le e z) := by
  obtain ⟨z0, hC0, hV0⟩ :=
    p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance H b hb e
  exact CompactZeroCovarianceResidualObstruction.not_allContext_variance_cap
    (V b hb.le e) (C b hb.le e) z0 hV0 hC0 theta htheta

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_originalGaugePath_zeroCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_exists_zeroCovariance_positiveVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_exists_zeroCovariance_fullDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_originalDefect_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_covarianceCapViolation_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_covarianceCapViolation_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_positiveVarianceViolation_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_no_ae_defect_covariance_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_no_allContext_defect_covariance_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_no_exists_ae_defect_covariance_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_varianceCapViolation_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_varianceCapViolation_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_no_ae_defect_variance_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACL_no_allContext_defect_variance_cap
