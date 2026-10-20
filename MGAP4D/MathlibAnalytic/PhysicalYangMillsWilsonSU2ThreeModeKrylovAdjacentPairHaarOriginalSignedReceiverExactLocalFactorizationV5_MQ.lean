import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTouchingLinkGIObstructionV5_MO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

/-!
# P4-Q2-MQ — EXACT locality of the original signed Wilson GI receiver
# AFTER removal of the genuine global positive Wilson kernel factor

In JH the actual original interacting Wilson posterior signed GI
receiver is represented by a continuous Haar-L² Riesz density
  r_(e,z)(A) =
     ∫_SU2 K_b(A, z.right[e:=g])
       * s(z.left,z.right[e:=g])⁻¹
       * (p_0(g)-p_pi(g)) dν(g).
It is essential that BOTH p_0 and p_pi are the TRUE ORIGINAL
interacting Wilson conditional posterior densities: none is replaced
by independent Haar.

The pre-existing exact physical right-link Wilson factorization is
  K_b(A,z.right[e:=g])
     = F_b(A(e),z.right,e,g) K_b(A,z.right),
where the TRUE factor F_b depends on the source-side configuration A
ONLY through its value A(e), while its other arguments retain the
original right spatial Wilson plaquette action around e.

This module transports the exact original factorization through the
ACTUAL signed posterior integral, obtaining the equality
  r_(e,z)(A) = K_b(A,z.right) * localProfile_(e,z)(A).
The profile integrates the original local factor against the
ORIGINAL density contrast and original positive joint half-density.
It depends on A ONLY through A(e). Since K_b>0, its exact normalized
signed Riesz quotient r/K has the same single-link locality.

For LW's original compensated physical signed GI bounded functional,
the genuine representing density is -s(z)r(A), so its quotient by
K_b(A,z.right) is exactly -s(z)*localProfile(A), still local in A(e).

CRITICAL distinction:
* TRUE unnormalized Riesz density r(A) has the nonlocal factor K(A,B)
  and is NOT asserted to be local in A.
* The ratio r(A)/K(A,B) is exactly receiver-link-local for fixed
  authentic interacting posterior context z. This is a structural
  factorization, not a proven decay of spatial Wilson correlations
  after integrating sources against K(A,B)dHaar(A).
* The localProfile is not a new physical detector or independent
  posterior; it is an exact rewriting of JH's old signed receiver.

This identifies the genuine remaining analytic task: covariance or
conditional mixing under the POSITIVE ORIGINAL interacting kernel
weight K(A,B), before transporting to fine endpoint source synthesis.
Volume-uniform H1-C3, positive fine × arbitrary Krylov separation,
OS/Wightman reconstruction and the 4D continuum mass gap remain OPEN.
No artificial axiom/rank/source, Dobrushin, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "delta" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "factor" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor H 2 b
local notation "r" => p4Q2JH_originalFiberRepresenter H b hb

/-- The EXACT ORIGINAL right-link Wilson factor depends on the
source-side configuration A only through the SINGLE source link
A(e), independently of all other source-side links. The full
underlying Wilson kernel still depends on every plaquette. -/
theorem p4Q2MQ_originalLocalFactor_eq_of_sourceReceiverLink_eq
    (A A' B : Cfg) (e : Link) (g : Gauge)
    (hAe : A e = A' e) :
    factor A B e g = factor A' B e g := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
  rw [hAe]

/-- The genuine original interacting posterior local profile, obtained
by inserting the ALREADY PROVED exact Wilson right-link local factor
into the original JH fiber density without changing the true signed
posterior contrast or physical joint half-density. -/
noncomputable def p4Q2MQ_originalSignedLocalFiberProfile
    (e : Link) (z : Cfg × Cfg) (A : Cfg) : ℝ :=
  ∫ g : Gauge,
    factor A z.2 e g *
      ((s (z.1, Function.update z.2 e g))⁻¹ *
        delta z.2 e g) ∂nu

local notation "localProfile" => p4Q2MQ_originalSignedLocalFiberProfile H b hb

/-- EXACT ORIGINAL Wilson signed-receiver Riesz density factorization:
the same JH Riesz representer equals the real original global positive
Wilson kernel K_b(A,z.right) TIMES the genuine one-link local signed
interacting-posterior profile. No fake detector or probability law. -/
theorem p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    r e z A = K A z.2 * localProfile e z A := by
  rw [p4Q2JH_originalFiberRepresenter_apply H b hb e z A]
  change
    (∫ g : Gauge,
      K A (Function.update z.2 e g) *
        (s (z.1, Function.update z.2 e g))⁻¹ *
          delta z.2 e g ∂nu) =
      K A z.2 *
        (∫ g : Gauge,
          factor A z.2 e g *
            ((s (z.1, Function.update z.2 e g))⁻¹ *
              delta z.2 e g) ∂nu)
  calc
    (∫ g : Gauge,
      K A (Function.update z.2 e g) *
        (s (z.1, Function.update z.2 e g))⁻¹ *
          delta z.2 e g ∂nu) =
      ∫ g : Gauge,
        K A z.2 *
          (factor A z.2 e g *
            ((s (z.1, Function.update z.2 e g))⁻¹ *
                delta z.2 e g)) ∂nu := by
      apply integral_congr_ae
      filter_upwards with g
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
        H 2 b A z.2 e g]
      ring
    _ = K A z.2 *
      (∫ g : Gauge,
        factor A z.2 e g *
          ((s (z.1, Function.update z.2 e g))⁻¹ *
            delta z.2 e g) ∂nu) := by rw [integral_const_mul]

/-- EXACT genuine local-profile invariance when the source-side
link A(e) is the same. Both original interacting posterior densities
and physical Wilson joint half-density remain fixed, NOT Haar-replaced. -/
theorem p4Q2MQ_originalSignedLocalProfile_eq_of_sourceReceiverLink_eq
    (e : Link) (z : Cfg × Cfg) (A A' : Cfg)
    (hAe : A e = A' e) :
    localProfile e z A = localProfile e z A' := by
  unfold p4Q2MQ_originalSignedLocalFiberProfile
  apply integral_congr_ae
  filter_upwards with g
  rw [p4Q2MQ_originalLocalFactor_eq_of_sourceReceiverLink_eq
    H b A A' z.2 e g hAe]

/-- Strict positivity of the real original Wilson kernel makes
the quotient of the original signed GI Riesz density exactly the
true SU(2) one-link interacting posterior local profile. -/
theorem p4Q2MQ_originalSignedRiesz_div_originalKernel_eq_localProfile
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    r e z A / K A z.2 = localProfile e z A := by
  have hK :
      K A z.2 ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2).ne'
  rw [p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile]
  field_simp [hK]

/-- The original *transfer-compensated* physical signed receiver
Riesz density is precisely -s(z)*r(A) by LW. Dividing by the
POSITIVE actual original Wilson kernel leaves the exact same
source receiver-link-local profile with its original signed
posterior, not a new detector or a change of physical source. -/
theorem p4Q2MQ_originalCompensatedSignedRiesz_normalized_eq_localProfile
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    (-(s z) * r e z A) / K A z.2 =
      -(s z) * localProfile e z A := by
  have hK :
      K A z.2 ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2).ne'
  rw [p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile]
  field_simp [hK]
  ring

/-- Exact SINGLE SOURCE LINK locality of the genuinely
transfer-compensated original signed interacting posterior Riesz
density AFTER division by its original global positive Wilson
kernel. In general the original uncompensated density is NOT local. -/
theorem p4Q2MQ_originalCompensatedSignedRiesz_quotient_local
    (e : Link) (z : Cfg × Cfg) (A A' : Cfg)
    (hAe : A e = A' e) :
    (-(s z) * r e z A) / K A z.2 =
      (-(s z) * r e z A') / K A' z.2 := by
  rw [p4Q2MQ_originalCompensatedSignedRiesz_normalized_eq_localProfile,
      p4Q2MQ_originalCompensatedSignedRiesz_normalized_eq_localProfile,
      p4Q2MQ_originalSignedLocalProfile_eq_of_sourceReceiverLink_eq
        H b hb e z A A' hAe]

/-- For a source-side link q different from the fixed authentic
receiver link e, the normalized genuine signed Riesz density is
pointwise UNCHANGED by arbitrary SU(2) q-link replacements. This
is a rigorous relative locality statement; it does NOT claim the
un-normalized receiver or its physical source GI response vanishes. -/
theorem p4Q2MQ_originalCompensatedSignedRiesz_quotient_update_outside
    (e q : Link) (z : Cfg × Cfg) (A : Cfg)
    (g h : Gauge) (hqe : q ≠ e) :
    (-(s z) * r e z (Function.update A q g)) /
        K (Function.update A q g) z.2 =
      (-(s z) * r e z (Function.update A q h)) /
        K (Function.update A q h) z.2 := by
  have hAe :
      (Function.update A q g) e =
        (Function.update A q h) e := by
    classical
    simp [Function.update, hqe]
  exact p4Q2MQ_originalCompensatedSignedRiesz_quotient_local
    H b hb e z (Function.update A q g) (Function.update A q h) hAe

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalLocalFactor_eq_of_sourceReceiverLink_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalSignedLocalProfile_eq_of_sourceReceiverLink_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalSignedRiesz_div_originalKernel_eq_localProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalCompensatedSignedRiesz_normalized_eq_localProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalCompensatedSignedRiesz_quotient_local
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MQ_originalCompensatedSignedRiesz_quotient_update_outside
