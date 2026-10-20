import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalCovarianceCauchyV5_MT
import Mathlib.Tactic

/-!
# P4-Q2-MU — original Wilson conditional covariance CS on actual physical GI source

MT proves original finite-volume SU(2) positive Wilson kernel-weighted
Cauchy-Schwarz using pinned mathlib Hölder p=q=2.
MS already identifies the original Gauss-law centered plaquette source's
physical signed GI response with the normalized original Wilson-kernel
covariance with MQ's true two-interacting-posterior signed local score.

This module proves, with NO independence/mixing premise, that the
MS original conditional expectation is linear, presents the EXISTING
signed posterior moment through MT's continuous REAL original one-link
score, and identifies the MS covariance with the exactly centered
original Wilson kernel-weighted inner product.

Consequently, for f an ORIGINAL continuous spatial source and Psi
the true local signed interacting-Wilson receiver profile:
    Cov_K(f,Psi)^2 <= Var_K(f) Var_K(Psi),
where all three moments use the SAME TRUE original positive one-slab
Wilson kernel K_b(A,B) and its proved-positive normalization M_H,b(B).
The second variance is literally the centered variance of the
EXISTING signed score, not an independent posterior density.

The exact original Gauss-law centered Wilson plaquette source
C_(H,p;B) of MS then obeys the physical quantitative upper bound
  [ (||T||/M) GI_(e,z)(C_(H,p;B)) ]²
     <= s(z)² Var_K(W_(H,p)) Var_K(Psi_(e,z)).

This is a finite-volume UPPER bound on the unchanged original
two-posterior receiver, not a spatial mixing decay, a positive lower
coercivity floor, fine-Krylov source separation, H1-C3, or a
continuum 4D Yang-Mills mass-gap proof. All remain OPEN.

No new physical source direction, detector, independent-Haar posterior,
Dobrushin input, sorry, admit, or axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "Mean" => p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "SignedMean" => p4Q2MS_originalSignedKernelConditionalMean H b hb
local notation "Cov" => p4Q2MS_originalWilsonKernelConditionalCovariance H b hb
local notation "Mass" => p4Q2MR_originalWilsonKernelMass H b
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "GI" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb
local notation "Centered" => p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource H b
local notation "Var" => p4Q2MS_originalWilsonKernelConditionalVariance H b

/-- Same original signed two-interacting-Wilson-posterior MQ score,
now in a continuous function presentation guaranteed by MT. -/
noncomputable def p4Q2MU_originalSignedWilsonScoreContinuous
    (e : Link) (z : Cfg × Cfg) : C(Cfg, ℝ) :=
  ⟨fun A => p4Q2MQ_originalSignedLocalFiberProfile H b hb e z A,
    p4Q2MT_originalSignedLocalProfile_continuous H b hb e z⟩

local notation "PsiC" => p4Q2MU_originalSignedWilsonScoreContinuous H b hb

/-- Genuine original Wilson K-normalized expectation respects ADDITION. -/
theorem p4Q2MU_originalWilsonMean_add
    (z : Cfg × Cfg) (f g : C(Cfg, ℝ)) :
    Mean z (f + g) = Mean z f + Mean z g := by
  have hk : Continuous (fun A : Cfg => K A z.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2
  have hf : Integrable (fun A : Cfg => f A * K A z.2) haar :=
    (f.continuous.mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun A : Cfg => g A * K A z.2) haar :=
    (g.continuous.mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ A : Cfg, (f A + g A) * K A z.2 ∂haar) / Mass z =
    (∫ A : Cfg, f A * K A z.2 ∂haar) / Mass z +
      (∫ A : Cfg, g A * K A z.2 ∂haar) / Mass z
  simp_rw [add_mul]
  rw [integral_add hf hg]
  ring

/-- Genuine original Wilson K-normalized expectation respects SUBTRACTION. -/
theorem p4Q2MU_originalWilsonMean_sub
    (z : Cfg × Cfg) (f g : C(Cfg, ℝ)) :
    Mean z (f - g) = Mean z f - Mean z g := by
  have hk : Continuous (fun A : Cfg => K A z.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2
  have hf : Integrable (fun A : Cfg => f A * K A z.2) haar :=
    (f.continuous.mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun A : Cfg => g A * K A z.2) haar :=
    (g.continuous.mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ A : Cfg, (f A - g A) * K A z.2 ∂haar) / Mass z =
    (∫ A : Cfg, f A * K A z.2 ∂haar) / Mass z -
      (∫ A : Cfg, g A * K A z.2 ∂haar) / Mass z
  simp_rw [sub_mul]
  rw [integral_sub hf hg]
  ring

/-- Genuine original Wilson K-normalized expectation respects REAL SCALARS. -/
theorem p4Q2MU_originalWilsonMean_smul
    (z : Cfg × Cfg) (c : ℝ) (f : C(Cfg, ℝ)) :
    Mean z (c • f) = c * Mean z f := by
  change (∫ A : Cfg, (c * f A) * K A z.2 ∂haar) / Mass z =
    c * ((∫ A : Cfg, f A * K A z.2 ∂haar) / Mass z)
  have h :
      (∫ A : Cfg, (c * f A) * K A z.2 ∂haar) =
      c * (∫ A : Cfg, f A * K A z.2 ∂haar) := by
    calc
      (∫ A : Cfg, (c * f A) * K A z.2 ∂haar) =
          ∫ A : Cfg, c * (f A * K A z.2) ∂haar := by
            apply integral_congr_ae
            filter_upwards with A
            ring
      _ = c * (∫ A : Cfg, f A * K A z.2 ∂haar) :=
        integral_const_mul _ _
  rw [h]
  ring

/-- The SAME original signed two-posterior profile moment coincides
with the original Wilson positive-kernel mean of f TIMES the authentic
continuous presentation of MQ's score. There is no substituted posterior. -/
theorem p4Q2MU_originalSignedMean_eq_mean_mul_score
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    SignedMean e z f = Mean z (f * PsiC e z) := by
  change
    (∫ A : Cfg, f A *
      (K A z.2 * p4Q2MQ_originalSignedLocalFiberProfile H b hb e z A) ∂haar) /
        Mass z =
      (∫ A : Cfg, (f A *
        p4Q2MQ_originalSignedLocalFiberProfile H b hb e z A) *
          K A z.2 ∂haar) / Mass z
  congr 1
  apply integral_congr_ae
  filter_upwards with A
  ring

/-- The pinned MT original Wilson positive-kernel Cauchy–Schwarz,
now divided ONLY by the PROVED-POSITIVE true Wilson kernel mass.
No independent sampling or artificially normalized detector. -/
theorem p4Q2MU_originalWilsonMean_cauchySchwarz
    (z : Cfg × Cfg) (f g : C(Cfg, ℝ)) :
    (Mean z (f * g))^2 ≤
      Mean z (f * f) * Mean z (g * g) := by
  have hMass : 0 < Mass z :=
    p4Q2MS_originalWilsonKernelMass_pos H b z
  have hMassSq : 0 < (Mass z)^2 := sq_pos_of_pos hMass
  have hCS :=
    p4Q2MT_originalWilsonKernel_weightedCauchySchwarz H b z f g
  have hCore :
      ((∫ A : Cfg, f A * g A * K A z.2 ∂haar) / Mass z)^2 ≤
        ((∫ A : Cfg, (f A)^2 * K A z.2 ∂haar) / Mass z) *
          ((∫ A : Cfg, (g A)^2 * K A z.2 ∂haar) / Mass z) := by
    calc
      ((∫ A : Cfg, f A * g A * K A z.2 ∂haar) / Mass z)^2 =
          (∫ A : Cfg, f A * g A * K A z.2 ∂haar)^2 /
            (Mass z)^2 := by ring
      _ ≤ ((∫ A : Cfg, (f A)^2 * K A z.2 ∂haar) *
             (∫ A : Cfg, (g A)^2 * K A z.2 ∂haar)) /
               (Mass z)^2 :=
        (div_le_div_iff_of_pos_right hMassSq).2 hCS
      _ = ((∫ A : Cfg, (f A)^2 * K A z.2 ∂haar) / Mass z) *
          ((∫ A : Cfg, (g A)^2 * K A z.2 ∂haar) / Mass z) := by ring
  simpa only [p4Q2MS_originalWilsonKernelConditionalMean,
    p4Q2MR_originalWilsonKernelMoment,
    ContinuousMap.mul_apply, pow_two] using hCore

/-- The MS true Wilson signed covariance is EXACTLY the original
positive-kernel average of TWO CENTERED ACTUAL CONTINUOUS OBSERVABLES:
f and MQ's real signed two-interacting-Wilson-posterior score. -/
theorem p4Q2MU_originalWilsonCovariance_eq_centeredMean
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    Cov e z f =
      Mean z
        ((f - (Mean z f) • (1 : C(Cfg, ℝ))) *
          (PsiC e z - (Mean z (PsiC e z)) • (1 : C(Cfg, ℝ)))) := by
  let q : C(Cfg, ℝ) := PsiC e z
  let mf : ℝ := Mean z f
  let mg : ℝ := Mean z q
  let fc : C(Cfg, ℝ) := f - mf • (1 : C(Cfg, ℝ))
  let gc : C(Cfg, ℝ) := q - mg • (1 : C(Cfg, ℝ))
  have hSignedF :=
    p4Q2MU_originalSignedMean_eq_mean_mul_score H b hb e z f
  have hSignedOne :=
    p4Q2MU_originalSignedMean_eq_mean_mul_score H b hb e z
      (1 : C(Cfg, ℝ))
  have hScoreOne : (1 : C(Cfg, ℝ)) * q = q := one_mul q
  change SignedMean e z (1 : C(Cfg, ℝ)) =
    Mean z ((1 : C(Cfg, ℝ)) * q) at hSignedOne
  rw [hScoreOne] at hSignedOne
  have hAlg :
      fc * gc =
        f * q - mg • f - mf • q + (mf * mg) • (1 : C(Cfg, ℝ)) := by
    ext A
    simp only [fc, gc, ContinuousMap.mul_apply,
      ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
    ring
  have hMeanExpand :
      Mean z (fc * gc) =
        Mean z (f * q) - mg * Mean z f -
          mf * Mean z q + mf * mg := by
    rw [hAlg]
    simp only [p4Q2MU_originalWilsonMean_add,
      p4Q2MU_originalWilsonMean_sub,
      p4Q2MU_originalWilsonMean_smul,
      p4Q2MS_originalWilsonKernelConditionalMean_one]
    ring
  change Cov e z f = Mean z (fc * gc)
  calc
    Cov e z f = Mean z (f * q) - mf * mg := by
      change SignedMean e z f -
        Mean z f * SignedMean e z (1 : C(Cfg, ℝ)) =
          Mean z (f * q) - mf * mg
      rw [hSignedF, hSignedOne]
    _ = Mean z (fc * gc) := by
      rw [hMeanExpand]
      dsimp [mf, mg]
      ring

/-- The original MS positive-kernel variance is the expectation
of the squared centered ACTUAL continuous Wilson source. -/
theorem p4Q2MU_originalWilsonVariance_eq_centeredMeanSq
    (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    Var z f =
      Mean z ((f - (Mean z f) • (1 : C(Cfg, ℝ))) *
        (f - (Mean z f) • (1 : C(Cfg, ℝ)))) := by
  unfold p4Q2MS_originalWilsonKernelConditionalVariance
    p4Q2MS_originalWilsonKernelConditionalMean
    p4Q2MR_originalWilsonKernelMoment
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one]
  congr 1
  apply integral_congr_ae
  filter_upwards with A
  ring

/-- The ACTUAL original signed two-posterior receiver score's
conditional variance under the SAME positive original Wilson kernel. -/
noncomputable def p4Q2MU_originalSignedScoreWilsonConditionalVariance
    (e : Link) (z : Cfg × Cfg) : ℝ :=
  let q : C(Cfg, ℝ) := PsiC e z
  let qc : C(Cfg, ℝ) := q - (Mean z q) • (1 : C(Cfg, ℝ))
  Mean z (qc * qc)

local notation "ScoreVar" => p4Q2MU_originalSignedScoreWilsonConditionalVariance H b hb

/-- The genuine original signed receiver score's K-conditional variance
is nonnegative. This is not a uniform variance lower bound. -/
theorem p4Q2MU_originalSignedScoreWilsonVariance_nonneg
    (e : Link) (z : Cfg × Cfg) :
    0 ≤ ScoreVar e z := by
  let q : C(Cfg, ℝ) := PsiC e z
  let qc : C(Cfg, ℝ) := q - (Mean z q) • (1 : C(Cfg, ℝ))
  change 0 ≤ (∫ A : Cfg, qc A * qc A * K A z.2 ∂haar) / Mass z
  apply div_nonneg
  · apply integral_nonneg
    intro A
    exact mul_nonneg (mul_self_nonneg _) <|
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le
  · exact (p4Q2MS_originalWilsonKernelMass_pos H b z).le

/-- The ACTUAL signed two-interacting-posterior conditional covariance
obeys TRUE Wilson kernel-weighted Cauchy-Schwarz with exact centered
MS variance and exact centered MQ score variance. -/
theorem p4Q2MU_originalWilsonConditionalCovariance_sq_le_variances
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    (Cov e z f)^2 ≤ Var z f * ScoreVar e z := by
  let fc : C(Cfg, ℝ) :=
    f - (Mean z f) • (1 : C(Cfg, ℝ))
  let q : C(Cfg, ℝ) := PsiC e z
  let gc : C(Cfg, ℝ) :=
    q - (Mean z q) • (1 : C(Cfg, ℝ))
  have hCS := p4Q2MU_originalWilsonMean_cauchySchwarz H b z fc gc
  have hCov :
      Cov e z f = Mean z (fc * gc) :=
    p4Q2MU_originalWilsonCovariance_eq_centeredMean H b hb e z f
  have hVar :
      Var z f = Mean z (fc * fc) :=
    p4Q2MU_originalWilsonVariance_eq_centeredMeanSq H b z f
  change (Cov e z f)^2 ≤ Var z f * ScoreVar e z
  calc
    (Cov e z f)^2 = (Mean z (fc * gc))^2 := by rw [hCov]
    _ ≤ Mean z (fc * fc) * Mean z (gc * gc) := hCS
    _ = Var z f * ScoreVar e z := by
      rw [hVar]
      rfl

/-- The SAME ORIGINAL centered Gauss-law physical Wilson plaquette
source of MS satisfies a quantitative GI response UPPER bound by
the PRODUCT of the exact true positive-Wilson kernel conditional
plaquette variance and original interacting-posterior score variance.
Not a physical coercivity lower bound, not spatial decay. -/
theorem p4Q2MU_originalPhysicalCenteredGI_sq_le_trueWilsonVariances
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    ((tN / Mass z) * GI (Centered z p) e z)^2 ≤
      (s z)^2 * (Var z (w p) * ScoreVar e z) := by
  have hEq := p4Q2MS_originalNormalizedPhysicalCenteredGI_eq_covariance
    H b hb e z p
  have hCS := p4Q2MU_originalWilsonConditionalCovariance_sq_le_variances
    H b hb e z (w p)
  have hs : 0 ≤ (s z)^2 := sq_nonneg _
  calc
    ((tN / Mass z) * GI (Centered z p) e z)^2 =
        (s z)^2 * (Cov e z (w p))^2 := by rw [hEq]; ring
    _ ≤ (s z)^2 * (Var z (w p) * ScoreVar e z) :=
      mul_le_mul_of_nonneg_left hCS hs

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonMean_add
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonMean_sub
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonMean_smul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalSignedMean_eq_mean_mul_score
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonMean_cauchySchwarz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonCovariance_eq_centeredMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonVariance_eq_centeredMeanSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalSignedScoreWilsonVariance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalWilsonConditionalCovariance_sq_le_variances
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MU_originalPhysicalCenteredGI_sq_le_trueWilsonVariances
