import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedReceiverExactLocalFactorizationV5_MQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedReceiverOneLinkOscillationV5_MP
import Mathlib.Tactic

/-!
# P4-Q2-MR — genuine original Wilson-kernel weighted connected physical GI response

MP proved volume-independent *single-link oscillation* of the SAME
original interacting Wilson two-posterior signed GI Riesz density.
MQ proved the crucial EXACT factorization of that density:

  r_(e,z)(A) = K_b(A,z.right) * Psi_(e,z)(A(e)),

where the full positive Wilson one-slab kernel K_b retains the
nonlocal spatial coupling, but Psi is a genuine one-link profile
computed from the TWO original interacting Wilson posterior rows.
The local Psi is NOT a replacement posterior or artificial detector.

MR converts this identity, with no changes to the original physical
source, into an EXACT ORIGINAL Wilson-kernel weighted covariance
numerator; it reuses the existing MQ local profile directly. For a real continuous spatial test f define

  M_0 = ∫_H K_b(A,z.right) dHaar_H(A),
  M_f = ∫_H f(A) K_b(A,z.right) dHaar_H(A),
  P_f = ∫_H f(A) K_b(A,z.right) Psi_(e,z)(A) dHaar_H(A).

For the real transfer-compensated original signed GI detector
  Q_(e,z)(f) = ||T|| G_(e,z)(f)
the actual physical kernel identity is
  Q_(e,z)(f) = -s(z) P_f.

It follows with NO spatial independence or decay assumption that
  M_0 Q_(e,z)(f) - M_f Q_(e,z)(1)
       = -s(z) (M_0 P_f - M_f P_1).

The RHS is exactly the UNNORMALIZED CONNECTED correlation between f
and the original receiver-link-local signed score Psi under the
positive *original interacting Wilson kernel weight* K_b. It is
not the covariance under independent Haar. This is an algebraic
identity of the TRUE Wilson integral and original GI detector, not
a spatial covariance decay theorem.

Crucially we specialize that connected identity to the ACTUAL
gauge-invariant Gauss-law Hilbert plaquette source W_{H,p} U of LO,
and the actual Gauss-law constant unit U, using the already proved
JH/LO/LM exact identification. The same signed source and actual
pair of interacting Wilson posteriors are retained at both ends.

The nonnegative true kernel mass M_0 is also proved directly from
the positive original Wilson kernel. A lower or uniform-in-H bound
on the connected correlation, an actual volume-independent spectral
gap, signed GI tail summability, fine endpoint intertwining,
positive fine-coupling all-Krylov separation, H1-C3 and continuum
4D Yang-Mills mass gap all remain OPEN.

No new independent-Haar posterior, Dobrushin, assumed mixing,
auxiliary rank, physical-source modification, sorry, admit or axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "r" => p4Q2JH_originalFiberRepresenter H b hb
local notation "Psi" => p4Q2MQ_originalSignedLocalFiberProfile H b hb
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "Q" => p4Q2LW_originalTransferCompensatedGIResponse H b hb
local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb
local notation "PhysicalGI" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Wp" => p4Q2LO_originalLocalPlaquettePhysicalSource H

/-- The ACTUAL original transfer-compensated signed Wilson GI Riesz
density is exactly the original positive Wilson kernel multiplied
by the existing MQ genuine two-interacting-posterior local profile.
No continuous-map duplicate or new detector is introduced. -/
theorem p4Q2MR_originalCompensatedSignedRiesz_eq_kernel_mul_profile
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    p4Q2MP_originalCompensatedSignedReceiverRieszDensity H b hb e z A =
      -(s z) * (K A z.2 * Psi e z A) := by
  change -(s z) * r e z A = -(s z) * (K A z.2 * Psi e z A)
  rw [p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile H b hb e z A]

/-- Total mass of the ORIGINAL strictly positive spatial Wilson kernel
section; NOT the mass of an invented independent-Haar posterior. -/
noncomputable def p4Q2MR_originalWilsonKernelMass (z : Cfg × Cfg) : ℝ :=
  ∫ A : Cfg, K A z.2 ∂haar

/-- True one-slab spatial Wilson kernel moment of an arbitrary original
continuous source f. The integral uses the existing spatial Haar carrier
only as the reference integration measure for the ACTUAL Wilson weight. -/
noncomputable def p4Q2MR_originalWilsonKernelMoment
    (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  ∫ A : Cfg, f A * K A z.2 ∂haar

/-- Signed Wilson-kernel profile moment with the EXACT original pair
of interacting posterior densities, NOT any independent resampling. -/
noncomputable def p4Q2MR_originalSignedWilsonProfileMoment
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  ∫ A : Cfg, f A * (K A z.2 * Psi e z A) ∂haar

local notation "Mass" => p4Q2MR_originalWilsonKernelMass H b
local notation "Moment" => p4Q2MR_originalWilsonKernelMoment H b
local notation "SignedMoment" => p4Q2MR_originalSignedWilsonProfileMoment H b hb

/-- Kernel mass is NONNEGATIVE at every finite original lattice, by
the exact positivity of the complete genuine Wilson slab kernel. -/
theorem p4Q2MR_originalWilsonKernelMass_nonneg (z : Cfg × Cfg) :
    0 ≤ Mass z := by
  unfold p4Q2MR_originalWilsonKernelMass
  apply integral_nonneg
  intro A
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
    H 2 b A z.2).le

/-- Core mathematical bridge: the exact original transfer-compensated
signed GI functional on EVERY continuous source f is an actual
Wilson-kernel weighted integral of the ONE-LINK signed posterior score.
No spatial correlation or mixing premise is used. -/
theorem p4Q2MR_originalCompensatedGI_eq_originalKernelWeightedProfile
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    Q e z (L f) = -(s z) * SignedMoment e z f := by
  let R := p4Q2MP_originalCompensatedSignedReceiverRieszDensity H b hb e z
  have hInner :
      Q e z (L f) = ∫ A : Cfg, f A * R A ∂haar := by
    rw [p4Q2MP_originalCompensatedSignedReceiver_eq_RieszDensity
      H b hb e z (L f)]
    exact ContinuousMap.inner_toLp haar R f
  have hEq :
      (∫ A : Cfg, f A * R A ∂haar) =
        ∫ A : Cfg, (-(s z)) *
          (f A * (K A z.2 * Psi e z A)) ∂haar := by
    apply integral_congr_ae
    filter_upwards with A
    change f A * (-(s z) * r e z A) =
      (-(s z)) * (f A * (K A z.2 * Psi e z A))
    rw [p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile
      H b hb e z A]
    ring
  calc
    Q e z (L f) = ∫ A : Cfg, f A * R A ∂haar := hInner
    _ = ∫ A : Cfg, (-(s z)) *
        (f A * (K A z.2 * Psi e z A)) ∂haar := hEq
    _ = -(s z) * SignedMoment e z f := by
      change (∫ A : Cfg, (-(s z)) *
        (f A * (K A z.2 * Psi e z A)) ∂haar) =
        -(s z) * ∫ A : Cfg,
          f A * (K A z.2 * Psi e z A) ∂haar
      rw [integral_const_mul]

/-- The genuine Gauss-law constant physical unit has an original
Wilson-kernel weighted signed response; no repeated fake anchor. -/
theorem p4Q2MR_originalPhysicalUnitGI_eq_originalKernelWeightedProfile
    (e : Link) (z : Cfg × Cfg) :
    tN * PhysicalGI U e z =
      -(s z) * SignedMoment e z (1 : C(Cfg, ℝ)) := by
  have h := p4Q2MR_originalCompensatedGI_eq_originalKernelWeightedProfile
    H b hb e z (1 : C(Cfg, ℝ))
  change tN * p4Q2JH_originalGIResponseCLM H b hb e z
    (L (1 : C(Cfg, ℝ))) =
      -(s z) * SignedMoment e z (1 : C(Cfg, ℝ)) at h
  rw [p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e z] at h
  exact h

/-- EXACT original signed GI response of an ACTUAL physical
Gauss-law source W_(H,p) U equals the original kernel-weighted score
moment of the same true SU(2) Wilson plaquette observable. -/
theorem p4Q2MR_originalPhysicalPlaquetteGI_eq_originalKernelWeightedProfile
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    tN * PhysicalGI (Wp p) e z =
      -(s z) * SignedMoment e z
        (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
  have h := p4Q2MR_originalCompensatedGI_eq_originalKernelWeightedProfile
    H b hb e z (p4Q2LO_originalLocalPlaquetteContinuous H p)
  change tN * p4Q2JH_originalGIResponseCLM H b hb e z
    (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) =
      -(s z) * SignedMoment e z
        (p4Q2LO_originalLocalPlaquetteContinuous H p) at h
  rw [p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI H b hb e z p] at h
  exact h

/-- The TRUE original Wilson-kernel-weighted connected correlation
NUMERATOR, not an assumed vanishing correlation or an invented law.
It is M_0 * M_(f*Score) - M_f * M_Score, with the same K and profile
derived from the genuine interacting signed GI receiver. -/
noncomputable def p4Q2MR_originalWilsonConnectedNumerator
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) : ℝ :=
  Mass z * SignedMoment e z f -
    Moment z f * SignedMoment e z (1 : C(Cfg, ℝ))

local notation "Connected" => p4Q2MR_originalWilsonConnectedNumerator H b hb

/-- Exact connected-response identity for ALL original continuous
spatial Wilson sources. This is the equation for the actual
Wilson-weighted covariance numerator and does not *assume* its size. -/
theorem p4Q2MR_originalCompensatedGI_centered_eq_connectedNumerator
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    Mass z * Q e z (L f) -
      Moment z f * Q e z (L (1 : C(Cfg, ℝ))) =
        -(s z) * Connected e z f := by
  rw [p4Q2MR_originalCompensatedGI_eq_originalKernelWeightedProfile
        H b hb e z f,
      p4Q2MR_originalCompensatedGI_eq_originalKernelWeightedProfile
        H b hb e z (1 : C(Cfg, ℝ))]
  unfold p4Q2MR_originalWilsonConnectedNumerator
  ring

/-- Genuine PHYSICAL local plaquette/source connected-response identity:
the same original positive Wilson kernel and the same two original
interacting-posterior GI rows are used for BOTH the constant Gauss-law
source and the real plaquette-multiplication Gauss-law source. The
remaining analytic object is the actual nonlocal Wilson-weighted
connected numerator, not geometric touching incidence alone. -/
theorem p4Q2MR_originalPhysicalPlaquetteGI_centered_eq_connectedNumerator
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    Mass z * (tN * PhysicalGI (Wp p) e z) -
      Moment z (p4Q2LO_originalLocalPlaquetteContinuous H p) *
        (tN * PhysicalGI U e z) =
      -(s z) * Connected e z
        (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
  rw [p4Q2MR_originalPhysicalPlaquetteGI_eq_originalKernelWeightedProfile
        H b hb e z p,
      p4Q2MR_originalPhysicalUnitGI_eq_originalKernelWeightedProfile
        H b hb e z]
  unfold p4Q2MR_originalWilsonConnectedNumerator
  ring

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalCompensatedSignedRiesz_eq_kernel_mul_profile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalWilsonKernelMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalCompensatedGI_eq_originalKernelWeightedProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalPhysicalUnitGI_eq_originalKernelWeightedProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalPhysicalPlaquetteGI_eq_originalKernelWeightedProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalCompensatedGI_centered_eq_connectedNumerator
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MR_originalPhysicalPlaquetteGI_centered_eq_connectedNumerator
