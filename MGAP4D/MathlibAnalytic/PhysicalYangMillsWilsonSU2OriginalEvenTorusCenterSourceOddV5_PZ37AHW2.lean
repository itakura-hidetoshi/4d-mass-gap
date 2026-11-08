import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterCochainV5_PZ37AHW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHW2 — true original center flux and source-odd Haar transport

Carry AHW's genuine even-torus Z/2 spatial center cochain through
the ACTUAL ordered SU(2) four-edge plaquette holonomy, without
commuting general SU(2) factors. Only true center signs are commuted.

The proved cochain has odd flux through every spatial plaquette.
The original Wilson trace of EVERY spatial plaquette therefore flips
sign under the explicit true-Haar-preserving spatial center twist.
The complete original centered ZW source consequently changes sign.

Apply the already proved AHV conditional Haar symmetry lemma to the
NOW CONSTRUCTED AND VERIFIED original center twist to establish
the genuine source cubic Haar moment M3_H=0 for all finite H.
AHU then gives the complete physical one-slab source-weighted
second-action moment M2_H(B) = (3*p_H+W_H(B))*V_H exactly.

The exact physical Gauss-law source, spatial Wilson action,
complete one-slab SU(2) kernel, both halfweights and Haar measures
are unchanged. No independent posterior, new axiom or surrogate.
This does not establish fixed-beta0 transfer sign, uniform coercivity,
Hamiltonian spectral gap or continuum 4D YM mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHW2_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHW2_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHW2_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHW2_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHW2_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "τ" => p4Q2PZ37AHW_originalCenterCochain H
local notation "s" => p4Q2PZ37AHW_originalCenterSign
local notation "T" => p4Q2PZ37AHW_originalCenterTwist H
local notation "z" => specialUnitaryTwoNegativeIdentity
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "M3" => p4Q2PZ37AHS_originalSourceThirdHaarMoment H
local notation "M2" => p4Q2PZ37AHS_originalSecondFullActionHaarMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2

local instance p4Q2PZ37AHW2_plaquettes : Fintype Plaq :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

local instance p4Q2PZ37AHW2_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Central rank-two SU(2) factors can be combined while respecting
the genuinely noncommuting original link variables. -/
theorem p4Q2PZ37AHW2_originalCenterSign_interleave
    (u v : G) (a b : ZMod 2) :
    (u * s a) * (v * s b) = (u * v) * s (a + b) := by
  calc
    (u * s a) * (v * s b) = (u * (s a * v)) * s b := by
      simp only [mul_assoc]
    _ = (u * (v * s a)) * s b := by
      rw [p4Q2PZ37AHW_originalCenterSign_commutes a v]
    _ = (u * v) * (s a * s b) := by
      simp only [mul_assoc]
    _ = (u * v) * s (a + b) := by
      rw [p4Q2PZ37AHW_originalCenterSign_add]

/-- The inverse-oriented genuine plaquette edges carry exactly the
same order-two central sign, not its inverse in a different order. -/
theorem p4Q2PZ37AHW2_originalCenterSign_inv_mul
    (u : G) (a : ZMod 2) :
    (u * s a)⁻¹ = u⁻¹ * s a := by
  rw [mul_inv_rev, p4Q2PZ37AHW_originalCenterSign_inv,
    p4Q2PZ37AHW_originalCenterSign_commutes a (u⁻¹)]

/-- Each true original ordered SU(2) spatial plaquette holonomy is
multiplied on the right by the actual central negative identity.
This proof retains all FOUR actual edges and inverse orientations. -/
theorem p4Q2PZ37AHW2_originalPlaquetteHolonomy_centerTwist
    (p : Plaq) (A : Cfg) :
    Hol (T A) p = Hol A p * z := by
  change
    (A (e0 p) * s (τ (e0 p))) *
      (A (e1 p) * s (τ (e1 p))) *
      (A (e2 p) * s (τ (e2 p)))⁻¹ *
      (A (e3 p) * s (τ (e3 p)))⁻¹ =
    (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) * z
  rw [p4Q2PZ37AHW2_originalCenterSign_inv_mul,
    p4Q2PZ37AHW2_originalCenterSign_inv_mul]
  rw [p4Q2PZ37AHW2_originalCenterSign_interleave,
    p4Q2PZ37AHW2_originalCenterSign_interleave,
    p4Q2PZ37AHW2_originalCenterSign_interleave]
  rw [p4Q2PZ37AHW_originalCenterCochain_plaquette H p,
    p4Q2PZ37AHW_originalCenterSign_one]

/-- Actual SU(2) normalized real plaquette trace is globally center-odd
on EVERY spatial plaquette at every genuine even periodic H. -/
theorem p4Q2PZ37AHW2_originalPlaquetteRealCharacter_centerTwist_odd
    (p : Plaq) (A : Cfg) :
    χ p (T A) = -(χ p A) := by
  unfold p4Q2PV_originalPlaquetteRealCharacter
  rw [p4Q2PZ37AHW2_originalPlaquetteHolonomy_centerTwist H p A,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring

/-- The full original Wilson spatial trace sum flips sign, including
every plaquette and the actual original finite summation. -/
theorem p4Q2PZ37AHW2_originalAllPlaquetteTrace_centerTwist_odd
    (A : Cfg) :
    Φ (T A) = -(Φ A) := by
  calc
    Φ (T A) = ∑ p : Plaq, χ p (T A) := rfl
    _ = ∑ p : Plaq, -(χ p A) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact p4Q2PZ37AHW2_originalPlaquetteRealCharacter_centerTwist_odd
        H p A
    _ = -(Φ A) := by
      rw [Finset.sum_neg_distrib]
      rfl

/-- Full original spatial Wilson action changes to its centered
complement under the explicit true center twist. -/
theorem p4Q2PZ37AHW2_originalSpatialWilson_centerTwist_complement
    (A : Cfg) :
    W (T A) = 2 * pH - W A := by
  have hs :=
    p4Q2PZ37AHR_originalSource_eq_negHalfTrace H (T A)
  have ht :=
    p4Q2PZ37AHR_originalSource_eq_negHalfTrace H A
  have hOdd :=
    p4Q2PZ37AHW2_originalAllPlaquetteTrace_centerTwist_odd H A
  have hAgg (B : Cfg) :=
    p4Q2PZ37AGN_originalCenteredContinuous_eq H B
  rw [hOdd] at hs
  rw [hAgg (T A)] at hs
  rw [hAgg A] at ht
  linarith only [hs, ht]

/-- The unchanged genuine ZW Gauss-law centered continuous source
is globally ODD under the explicitly constructed original-Haar
preserving spatial center twist. -/
theorem p4Q2PZ37AHW2_originalSource_centerTwist_odd
    (A : Cfg) :
    fCont (T A) = -(fCont A) := by
  rw [p4Q2PZ37AHR_originalSource_eq_negHalfTrace H (T A),
    p4Q2PZ37AHR_originalSource_eq_negHalfTrace H A,
    p4Q2PZ37AHW2_originalAllPlaquetteTrace_centerTwist_odd H A]
  ring

/-- The authentic previously unknown original SU(2) source THIRD Haar
moment vanishes exactly at ALL finite even periods. This DISCHARGES
AHV's conditional source-odd Haar transformation with the explicit
measure-preserving physical-link center twist, not a new axiom. -/
theorem p4Q2PZ37AHW2_originalSourceThirdMoment_zero :
    M3 = 0 := by
  exact p4Q2PZ37AHV_originalSourceThirdMoment_zero_of_oddHaar H
    T
    (p4Q2PZ37AHW_originalCenterTwist_Haar_measurePreserving H)
    (p4Q2PZ37AHW2_originalSource_centerTwist_odd H)

/-- Exact genuine one-slab SU(2) Wilson second SOURCE-weighted
ACTION moment now has no unevaluated cubic or mixed Haar intercept.
This is still NOT a spectral-gap assertion. -/
theorem p4Q2PZ37AHW2_originalSecondFullActionMoment_exact
    (B : Cfg) :
    M2 B = (3 * pH + W B) * Vsrc := by
  rw [p4Q2PZ37AHU_originalSecondFullActionMoment_exactMixed H B,
    p4Q2PZ37AHW2_originalSourceThirdMoment_zero H]
  ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalCenterSign_interleave
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalCenterSign_inv_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalPlaquetteHolonomy_centerTwist
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalPlaquetteRealCharacter_centerTwist_odd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalAllPlaquetteTrace_centerTwist_odd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalSpatialWilson_centerTwist_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalSource_centerTwist_odd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalSourceThirdMoment_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW2_originalSecondFullActionMoment_exact
