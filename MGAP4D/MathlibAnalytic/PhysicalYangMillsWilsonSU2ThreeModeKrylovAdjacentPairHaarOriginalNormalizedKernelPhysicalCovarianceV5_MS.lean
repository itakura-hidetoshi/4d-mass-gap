import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalKernelWeightedSignedPhysicalCovarianceV5_MR
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferProjectedTail
import Mathlib.Tactic

/-!
# P4-Q2-MS — normalized TRUE Wilson kernel and centered physical GI covariance

MR identifies the original SU(2) interacting-Wilson signed two-posterior
GI response of ACTUAL Gauss-law physical sources with an UNNORMALIZED
connected integral for the original positive one-slab Wilson kernel.

MS proves the real kernel-section normalizer M_H,b(B) is STRICTLY POSITIVE
(and at most one) at every finite spatial H, using the original strictly
positive Wilson slab kernel and its actual normalized spatial Haar
integration carrier. No model or posterior distribution is substituted.

The corresponding scalar conditional expectation is literally
  E_K[f] = (∫ f(A) K_b(A,B) dHaar_H(A)) / M_H,b(B).
This is a normalized *Wilson kernel SECTION* at the fixed actual right
boundary B, NOT the Perron-stationary Doob process or an independent-Haar
posterior. It is a real mathematical normalization of the already
present original physical transfer kernel, never a new physical detector.

For the original exact one-link signed interacting-posterior score
Psi_(e,z)(A(e)) from MQ define
  Cov_K(f,Psi) = E_K[f Psi] - E_K[f] E_K[Psi].
Then MR's genuine connected numerator equals M_H,b(B)^2 Cov_K.

Critically we select the ACTUAL gauge-invariant Gauss-law Hilbert source
  C_(H,p;B) := W_(H,p) U - E_K[W_(H,p)] U,
implemented through the EXISTING LO original physical two-source
construction, not a synthetic Hilbert direction or assumed rank.
For every true frozen interacting-Wilson posterior context z,
  (||T|| / M_H,b(z.right)) *
       GI_(e,z)(C_(H,p;z.right))
        = -s(z) * Cov_K(W_(H,p),Psi_(e,z)).
Thus the open spatial-mixing/scale-uniform question becomes a
quantitative problem for the TRUE positive Wilson-kernel conditional
covariance, with no artificial posterior or positive floor.

We also define its EXACT nonnegative variance at finite H. This alone
does NOT prove any spatial correlation decay, variance lower bound,
uniform volume nondegeneracy, positive-fine × arbitrary Krylov source
separation, H1-C3, or a continuum Yang–Mills mass gap.

No Dobrushin, independent-Haar replacement, sorry, admit, new axiom,
or replacement of the original Gauss-law physical source Hilbert space.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb
local notation "GI" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Wp" => p4Q2LO_originalLocalPlaquettePhysicalSource H
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "Mass" => p4Q2MR_originalWilsonKernelMass H b
local notation "Moment" => p4Q2MR_originalWilsonKernelMoment H b
local notation "SignedMoment" => p4Q2MR_originalSignedWilsonProfileMoment H b hb
local notation "Connected" => p4Q2MR_originalWilsonConnectedNumerator H b hb

/-- STRICT original Wilson one-slab kernel-section mass positivity at
every finite original spatial lattice and all frozen b >= 0.
No new probability distribution or compactness minimum is assumed. -/
theorem p4Q2MS_originalWilsonKernelMass_pos (z : Cfg × Cfg) :
    0 < Mass z := by
  let k : Cfg → ℝ := fun A => K A z.2
  have hk_nonneg : 0 ≤ k := fun A =>
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2).le
  have hk_int : Integrable k haar := by
    have hc : Continuous k :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
        H 2 b z.2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsupp : Function.support k = Set.univ := by
    ext A
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2).ne'
  change 0 < ∫ A : Cfg, k A ∂haar
  rw [integral_pos_iff_support_of_nonneg hk_nonneg hk_int, hsupp]
  simp

/-- The unnormalized TRUE original kernel-section mass is <= 1,
because 0 < K_b(A,B) <= 1 pointwise and spatial reference Haar has
mass one. Thus 0 < M_H,b(B) <= 1 at every finite H. -/
theorem p4Q2MS_originalWilsonKernelMass_le_one
    (hpos : 0 ≤ b) (z : Cfg × Cfg) :
    Mass z ≤ 1 := by
  let k : Cfg → ℝ := fun A => K A z.2
  have hk_int : Integrable k haar := by
    have hc : Continuous k :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
        H 2 b z.2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hupper : ∀ A : Cfg, k A ≤ (1 : ℝ) := by
    intro A
    exact (abs_le.mp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H 2 (by norm_num) b hpos A z.2)).2
  have hInt : (∫ A : Cfg, k A ∂haar) ≤
      ∫ _A : Cfg, (1 : ℝ) ∂haar :=
    integral_mono hk_int (integrable_const _) hupper
  change (∫ A : Cfg, k A ∂haar) ≤ 1
  simpa using hInt

/-- Unit moment equals the EXACT original positive Wilson kernel mass. -/
theorem p4Q2MS_originalWilsonKernelMoment_one_eq_mass
    (z : Cfg × Cfg) :
    Moment z (1 : C(Cfg, ℝ)) = Mass z := by
  unfold p4Q2MR_originalWilsonKernelMoment p4Q2MR_originalWilsonKernelMass
  simp

/-- Literal kernel-normalized scalar expectation for the same
positive original Wilson one-slab kernel section and actual Haar
integration carrier; not a postulated new physical posterior law. -/
noncomputable def p4Q2MS_originalWilsonKernelConditionalMean
    (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  Moment z f / Mass z

/-- Genuine signed two-interacting-Wilson-posterior profile moment
normalized by the SAME original Wilson kernel mass. -/
noncomputable def p4Q2MS_originalSignedKernelConditionalMean
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  SignedMoment e z f / Mass z

local notation "Mean" => p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "SignedMean" => p4Q2MS_originalSignedKernelConditionalMean H b hb

/-- The genuine Wilson-kernel conditional expectation preserves one,
since its denominator is proven STRICTLY positive, not just nonnegative. -/
theorem p4Q2MS_originalWilsonKernelConditionalMean_one
    (z : Cfg × Cfg) :
    Mean z (1 : C(Cfg, ℝ)) = 1 := by
  have hM : Mass z ≠ 0 := (p4Q2MS_originalWilsonKernelMass_pos H b z).ne'
  change Moment z (1 : C(Cfg, ℝ)) / Mass z = 1
  rw [p4Q2MS_originalWilsonKernelMoment_one_eq_mass H b z]
  exact div_self hM

/-- Original Wilson positive-kernel conditional covariance of a real
source f and the EXACT genuine signed interacting-posterior one-link
profile Psi. It is the normalized MR connected numerator. -/
noncomputable def p4Q2MS_originalWilsonKernelConditionalCovariance
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  SignedMean e z f -
    Mean z f * SignedMean e z (1 : C(Cfg, ℝ))

local notation "Cov" => p4Q2MS_originalWilsonKernelConditionalCovariance H b hb

/-- Exact original covariance numerator identity:
  M_H,b(B)^2 Cov_K(f,Psi) = MR's SAME genuine connected GI numerator.
No independence, cluster decay or mixed-posterior substitution. -/
theorem p4Q2MS_originalWilsonKernelCovariance_mul_mass_sq_eq_connected
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    (Mass z)^2 * Cov e z f = Connected e z f := by
  have hM : Mass z ≠ 0 := (p4Q2MS_originalWilsonKernelMass_pos H b z).ne'
  change (Mass z)^2 *
      (SignedMoment e z f / Mass z -
        (Moment z f / Mass z) *
          (SignedMoment e z (1 : C(Cfg, ℝ)) / Mass z)) =
    Mass z * SignedMoment e z f -
      Moment z f * SignedMoment e z (1 : C(Cfg, ℝ))
  field_simp [hM]

/-- The original normalized Wilson-kernel variance of any continuous
spatial source; a TRUE positive-kernel centered square integral. -/
noncomputable def p4Q2MS_originalWilsonKernelConditionalVariance
    (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  (∫ A : Cfg, (f A - Mean z f)^2 * K A z.2 ∂haar) / Mass z

/-- Exact TRUE positive Wilson-kernel variance is always >= 0.
No variance floor is assumed; nondegeneracy is still OPEN. -/
theorem p4Q2MS_originalWilsonKernelConditionalVariance_nonneg
    (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    0 ≤ p4Q2MS_originalWilsonKernelConditionalVariance H b z f := by
  unfold p4Q2MS_originalWilsonKernelConditionalVariance
  apply div_nonneg
  · apply integral_nonneg
    intro A
    exact mul_nonneg (sq_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le
  · exact (p4Q2MS_originalWilsonKernelMass_pos H b z).le

/-- GENUINE Gauss-law Hilbert source obtained by physically centering
the ACTUAL p-local original Wilson multiplication of U against the
ORIGINAL Wilson kernel section. It reuses LO's established physical
two-source plane; its coefficient is the actual kernel conditional mean. -/
noncomputable def p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource
    (z : Cfg × Cfg) (p : Plaq) : Phys :=
  p4Q2LO_originalPhysicalLocalTwoSource H p (-(Mean z (w p))) 1

local notation "CenteredSrc" => p4Q2MS_originalPhysicalCenteredWilsonPlaquetteSource H b

/-- The centered original physical source response is EXACTLY the
physical local plaquette signed GI response minus its true
Wilson-kernel mean times the genuine Gauss-law unit GI response.
No substitute gauge source, artificial direction or new receiver. -/
theorem p4Q2MS_originalPhysicalCenteredWilsonGI_eq_sourceDifference
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    GI (CenteredSrc z p) e z =
      GI (Wp p) e z - Mean z (w p) * GI U e z := by
  change GI (p4Q2LO_originalPhysicalLocalTwoSource H p (-(Mean z (w p))) 1) e z =
    GI (Wp p) e z - Mean z (w p) * GI U e z
  rw [p4Q2LO_originalPhysicalLocalTwoSource_GI_eq
        H b hb e z p (-(Mean z (w p))) 1,
      p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e z,
      p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI H b hb e z p]
  ring

/-- MR's actual physical Gauss-law plaquette/unit connected identity
becomes a true normalized one-slab Wilson kernel COVARIANCE,
without any new mixing assumption or posterior substitution. -/
theorem p4Q2MS_originalPhysicalCenteredWilsonGI_eq_mass_sq_covariance
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    Mass z * (tN * GI (CenteredSrc z p) e z) =
      -(s z) * ((Mass z)^2 * Cov e z (w p)) := by
  have hM : Mass z ≠ 0 := (p4Q2MS_originalWilsonKernelMass_pos H b z).ne'
  have hMean : Mass z * Mean z (w p) = Moment z (w p) := by
    change Mass z * (Moment z (w p) / Mass z) = Moment z (w p)
    field_simp [hM]
  have hPhys :=
    p4Q2MS_originalPhysicalCenteredWilsonGI_eq_sourceDifference H b hb e z p
  have hMR :=
    p4Q2MR_originalPhysicalPlaquetteGI_centered_eq_connectedNumerator
      H b hb e z p
  have hCov :=
    p4Q2MS_originalWilsonKernelCovariance_mul_mass_sq_eq_connected
      H b hb e z (w p)
  calc
    Mass z * (tN * GI (CenteredSrc z p) e z) =
        Mass z * (tN * GI (Wp p) e z) -
          Moment z (w p) * (tN * GI U e z) := by
            rw [hPhys, ← hMean]
            ring
    _ = -(s z) * Connected e z (w p) := hMR
    _ = -(s z) * ((Mass z)^2 * Cov e z (w p)) := by
      rw [hCov]

/-- FINAL exact true physical source/covariance bridge:
the same original Gauss-law centered Wilson p-source has its
signed two-interacting-Wilson-posterior GI response identified
precisely with the normalized genuine positive Wilson-kernel
covariance of that p-local Wilson observable and MQ's local score.

The original transfer norm tN and mass M are both actual >0,
not artificial normalization parameters. -/
theorem p4Q2MS_originalNormalizedPhysicalCenteredGI_eq_covariance
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    (tN / Mass z) * GI (CenteredSrc z p) e z =
      -(s z) * Cov e z (w p) := by
  have hM : Mass z ≠ 0 := (p4Q2MS_originalWilsonKernelMass_pos H b z).ne'
  have h :=
    p4Q2MS_originalPhysicalCenteredWilsonGI_eq_mass_sq_covariance
      H b hb e z p
  calc
    (tN / Mass z) * GI (CenteredSrc z p) e z =
        (Mass z * (tN * GI (CenteredSrc z p) e z)) / (Mass z)^2 := by
          field_simp [hM]
    _ = (-(s z) * ((Mass z)^2 * Cov e z (w p))) / (Mass z)^2 := by
      rw [h]
    _ = -(s z) * Cov e z (w p) := by
      field_simp [hM]

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalWilsonKernelMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalWilsonKernelMass_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalWilsonKernelMoment_one_eq_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalWilsonKernelConditionalMean_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalWilsonKernelCovariance_mul_mass_sq_eq_connected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalWilsonKernelConditionalVariance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalPhysicalCenteredWilsonGI_eq_sourceDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalPhysicalCenteredWilsonGI_eq_mass_sq_covariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MS_originalNormalizedPhysicalCenteredGI_eq_covariance
