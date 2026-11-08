import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrimitiveNegativeHaarFloorV5_PZ37AIJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIK — elementary original negative Haar floor

Unfold the ACTUAL pinned mathlib toSphereBallBound used by ADQ. For r>0,
  kappa(r) = (min(r,2)/4)^4,
and kappa(1/96) = (1/384)^4. The nonpositive-radius fallback is separate;
it is not a valid geometric floor at nonpositive radius.

Consequently the existing AIJ variance floor, margin and radius are
EXACTLY equal to expressions involving only beta, the original counts,
rational arithmetic, finite powers and exp. The authentic product-Haar
floor becomes
  (min(r_H(beta)/(n_H+1),2)/4)^(4*n_H).
No replacement sphere law, cap-volume formula, new sign assumption or
unproved monotonicity is used. ADZ's already-proved original SU(2) bridge
and AHL's original product-Haar ball theorem remain the geometric source.

Keep the complete Wilson kernel, both spatial halfweights, the signed ZW
physical L2 source, the same full-margin AIG negative region, all existing
proofs, assumptions, pins and workflow. This evaluates the previous
geometric certificate; it does not assert the exact Haar ball mass or an
optimal small-radius exponent. All volume dependence is explicit.
No evaluated negative center, positive-transfer boundary, both-sign
region, volume-uniform coercivity, Hamiltonian or continuum gap follows.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AIK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIK_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

/-- Unfold the exact pinned certificate only on its geometric domain.
The four-dimensional prefactor cancels ADQ's normalization denominator. -/
theorem p4Q2PZ37AIK_sphereRadiusFraction_eq
    (r : ℝ) (hr : 0 < r) :
    kappa r = (min r 2 / 4) ^ 4 := by
  unfold p4Q2PZ37ADQ_sphereRadiusFraction Measure.toSphereBallBound
  rw [if_pos ⟨by norm_num, hr⟩]
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_min, NNReal.coe_ofNat, Real.coe_toNNReal r hr.le]
  ring

/-- The nonpositive-radius fallback is distinct from the geometric branch.
In particular no monotonicity on all real radii is being assumed. -/
theorem p4Q2PZ37AIK_sphereRadiusFraction_of_nonpos
    (r : ℝ) (hr : r ≤ 0) : kappa r = 1 / 4 := by
  unfold p4Q2PZ37ADQ_sphereRadiusFraction Measure.toSphereBallBound
  rw [if_neg (fun h => (not_lt_of_ge hr) h.2)]
  rfl

/-- On the positive small-radius range the original certificate is quartic. -/
theorem p4Q2PZ37AIK_sphereRadiusFraction_eq_quartic
    (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
    kappa r = (r / 4) ^ 4 := by
  rw [p4Q2PZ37AIK_sphereRadiusFraction_eq r hr, min_eq_left hr2]

/-- Exact rational value used in the original identity source box. -/
theorem p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius :
    kappa (1 / 96) = (1 / 384 : ℝ) ^ 4 := by
  rw [p4Q2PZ37AIK_sphereRadiusFraction_eq_quartic (1 / 96)
    (by norm_num) (by norm_num)]
  norm_num

/-- Fully evaluated rational denominator, checked by exact arithmetic. -/
theorem p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius_rational :
    kappa (1 / 96) = (1 / 21743271936 : ℝ) := by
  rw [p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius]
  norm_num

/-- Evaluate the same certified fraction at an arbitrary finite power. -/
theorem p4Q2PZ37AIK_sphereRadiusFraction_pow
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    kappa r ^ n = (min r 2 / 4) ^ (4 * n) := by
  rw [p4Q2PZ37AIK_sphereRadiusFraction_eq r hr, pow_mul]

/-- The elementary expression bounds the ACTUAL normalized SU(2) Haar
ball, using the already discharged ADZ measure-transport bridge. -/
theorem p4Q2PZ37AIK_originalOneLinkBall_mass_ge_elementary
    (a : G) (r : ℝ) (hr : 0 < r) :
    (min r 2 / 4) ^ 4 ≤
      Measure.real (normalizedCompactHaar G)
        (p4Q2PZ37ADK_trueChordalBall a r) := by
  rw [← p4Q2PZ37AIK_sphereRadiusFraction_eq r hr]
  exact p4Q2PZ37ADZ_originalAllCenters_ge_explicit a r hr

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nH" => Nat.card Link
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "Rold" => p4Q2PZ37AIH_originalNegativeBallRadius H
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Ball" => p4Q2PZ37AHL_originalSpatialBall H

local instance p4Q2PZ37AIK_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Evaluate AHL's original product-Haar certificate at EVERY positive
spatial radius, retaining the original link count and all centers. -/
theorem p4Q2PZ37AIK_originalSpatialBall_mass_ge_elementary
    (B : Cfg) (R : ℝ) (hR : 0 < R) :
    (min (R / ((nH : ℝ) + 1)) 2 / 4) ^ (4 * nH) ≤
      Measure.real muH (Ball B R) := by
  have hr : 0 < R / ((nH : ℝ) + 1) := div_pos hR (by positivity)
  rw [← p4Q2PZ37AIK_sphereRadiusFraction_pow _ hr nH]
  simpa only [Fintype.card_eq_nat_card] using
    p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B R hR

/-- Exact elementary evaluation of AIJ's identity-box variance floor. -/
def p4Q2PZ37AIK_elementarySourceVarianceFloor : ℝ :=
  (3 * pH / 8) ^ 2 * (1 / 384 : ℝ) ^ (4 * nH)

local notation "v" => p4Q2PZ37AIK_elementarySourceVarianceFloor H

theorem p4Q2PZ37AIK_elementarySourceVarianceFloor_eq :
    v = p4Q2PZ37AIJ_sourceVarianceFloor H := by
  simp only [p4Q2PZ37AIK_elementarySourceVarianceFloor,
    p4Q2PZ37AIJ_sourceVarianceFloor,
    p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius, pow_mul]

theorem p4Q2PZ37AIK_elementarySourceVarianceFloor_pos : 0 < v := by
  rw [p4Q2PZ37AIK_elementarySourceVarianceFloor_eq]
  exact p4Q2PZ37AIJ_sourceVarianceFloor_pos H

theorem p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original : v ≤ Vsrc := by
  rw [p4Q2PZ37AIK_elementarySourceVarianceFloor_eq]
  exact p4Q2PZ37AIJ_sourceVarianceFloor_le_original H

/-- Same AIJ margin, now with no unevaluated integral or geometric constant. -/
def p4Q2PZ37AIK_elementaryNegativeMargin (beta : ℝ) : ℝ :=
  beta * Real.exp (-(2 * beta * ((nH : ℝ) + pH))) * v / 2

local notation "delta" => p4Q2PZ37AIK_elementaryNegativeMargin H

theorem p4Q2PZ37AIK_elementaryNegativeMargin_eq (beta : ℝ) :
    delta beta = p4Q2PZ37AIJ_primitiveNegativeMargin H beta := by
  unfold p4Q2PZ37AIK_elementaryNegativeMargin
    p4Q2PZ37AIJ_primitiveNegativeMargin
  rw [p4Q2PZ37AIK_elementarySourceVarianceFloor_eq]

theorem p4Q2PZ37AIK_elementaryNegativeMargin_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < delta beta := by
  rw [p4Q2PZ37AIK_elementaryNegativeMargin_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeMargin_pos H beta hbeta

theorem p4Q2PZ37AIK_elementaryNegativeMargin_zero : delta 0 = 0 := by
  rw [p4Q2PZ37AIK_elementaryNegativeMargin_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeMargin_zero H

theorem p4Q2PZ37AIK_elementaryNegativeMargin_le_original
    (beta : ℝ) (hbeta : 0 ≤ beta) : delta beta ≤ margin beta := by
  rw [p4Q2PZ37AIK_elementaryNegativeMargin_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeMargin_le_original H beta hbeta

/-- Exact AIJ radius with only beta, original counts and elementary operations. -/
def p4Q2PZ37AIK_elementaryNegativeBallRadius (beta : ℝ) : ℝ :=
  delta beta / (13 * beta * pH + 2)

local notation "r" => p4Q2PZ37AIK_elementaryNegativeBallRadius H

theorem p4Q2PZ37AIK_elementaryNegativeBallRadius_eq (beta : ℝ) :
    r beta = p4Q2PZ37AIJ_primitiveNegativeBallRadius H beta := by
  unfold p4Q2PZ37AIK_elementaryNegativeBallRadius
    p4Q2PZ37AIJ_primitiveNegativeBallRadius
  rw [p4Q2PZ37AIK_elementaryNegativeMargin_eq]

theorem p4Q2PZ37AIK_elementaryNegativeBallRadius_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < r beta := by
  rw [p4Q2PZ37AIK_elementaryNegativeBallRadius_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeBallRadius_pos H beta hbeta

theorem p4Q2PZ37AIK_elementaryNegativeBallRadius_le_original
    (beta : ℝ) (hbeta : 0 < beta) : r beta ≤ Rold beta (margin beta) := by
  rw [p4Q2PZ37AIK_elementaryNegativeBallRadius_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeBallRadius_le_original H beta hbeta

/-- Closed finite-volume lower mass, with the radius saturation kept exact.
The formula is used as a positive Haar floor only when beta>0. -/
def p4Q2PZ37AIK_elementaryNegativeHaarFloor (beta : ℝ) : ℝ :=
  (min (r beta / ((nH : ℝ) + 1)) 2 / 4) ^ (4 * nH)

local notation "m" => p4Q2PZ37AIK_elementaryNegativeHaarFloor H

/-- Exact equality with AIJ's floor, not an unsupported monotonicity step. -/
theorem p4Q2PZ37AIK_elementaryNegativeHaarFloor_eq
    (beta : ℝ) (hbeta : 0 < beta) :
    m beta =
      kappa (p4Q2PZ37AIJ_primitiveNegativeBallRadius H beta /
        ((nH : ℝ) + 1)) ^ nH := by
  have hr : 0 < r beta / ((nH : ℝ) + 1) :=
    div_pos (p4Q2PZ37AIK_elementaryNegativeBallRadius_pos H beta hbeta)
      (by positivity)
  unfold p4Q2PZ37AIK_elementaryNegativeHaarFloor
  rw [← p4Q2PZ37AIK_sphereRadiusFraction_pow _ hr nH,
    p4Q2PZ37AIK_elementaryNegativeBallRadius_eq]

theorem p4Q2PZ37AIK_elementaryNegativeHaarFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < m beta := by
  rw [p4Q2PZ37AIK_elementaryNegativeHaarFloor_eq H beta hbeta]
  exact pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _

/-- The unchanged full original negative threshold holds on this exact
elementary-radius ball around the already-proved original center. -/
theorem p4Q2PZ37AIK_elementaryNegativeBall_fullMargin_stable
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg)
    (hB : T beta f0 B < -(3 * margin beta / 2)) :
    ∀ C ∈ Ball B (r beta), T beta f0 C < -(margin beta) := by
  rw [p4Q2PZ37AIK_elementaryNegativeBallRadius_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeBall_fullMargin_stable H beta hbeta B hB

theorem p4Q2PZ37AIK_elementaryNegativeBall_mass_ge
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) :
    m beta ≤ Measure.real muH (Ball B (r beta)) := by
  exact p4Q2PZ37AIK_originalSpatialBall_mass_ge_elementary H B (r beta)
    (p4Q2PZ37AIK_elementaryNegativeBallRadius_pos H beta hbeta)

/-- Genuine negative boundary and quantitative original Haar ball for
every finite H and every beta>0, using the closed elementary certificate. -/
theorem p4Q2PZ37AIK_originalTransfer_exists_elementaryNegativeHaarBall
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg,
      T beta f0 B < -(3 * margin beta / 2) ∧
      0 < r beta ∧
      (∀ C ∈ Ball B (r beta), T beta f0 C < -(margin beta)) ∧
      0 < m beta ∧
      m beta ≤ Measure.real muH (Ball B (r beta)) := by
  obtain ⟨B, hB⟩ :=
    p4Q2PZ37AII_originalTransfer_exists_below_threeHalfMargin H beta hbeta
  exact ⟨B, hB,
    p4Q2PZ37AIK_elementaryNegativeBallRadius_pos H beta hbeta,
    p4Q2PZ37AIK_elementaryNegativeBall_fullMargin_stable H beta hbeta B hB,
    p4Q2PZ37AIK_elementaryNegativeHaarFloor_pos H beta hbeta,
    p4Q2PZ37AIK_elementaryNegativeBall_mass_ge H beta hbeta B⟩

/-- The closed expression bounds the SAME original AIG full-margin region. -/
theorem p4Q2PZ37AIK_originalFullNegativeRegion_elementaryMass
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < m beta ∧ m beta ≤ Measure.real muH (Region beta) := by
  rw [p4Q2PZ37AIK_elementaryNegativeHaarFloor_eq H beta hbeta]
  exact p4Q2PZ37AIJ_originalFullNegativeRegion_primitiveMass H beta hbeta

/-- Distinguish the larger sublevel at the elementary threshold from the
unchanged AIG full-margin region; it inherits the same certified floor. -/
theorem p4Q2PZ37AIK_elementaryNegativeRegion_mass
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < m beta ∧
      m beta ≤ Measure.real muH {C : Cfg | T beta f0 C < -(delta beta)} := by
  rw [p4Q2PZ37AIK_elementaryNegativeHaarFloor_eq H beta hbeta,
    p4Q2PZ37AIK_elementaryNegativeMargin_eq]
  exact p4Q2PZ37AIJ_primitiveNegativeRegion_mass H beta hbeta

/-- Retain the previous AII certificate and the evaluated AIJ certificate. -/
theorem p4Q2PZ37AIK_originalFullNegativeRegion_combinedMass
    (beta : ℝ) (hbeta : 0 < beta) :
    max (m beta)
      (kappa (Rold beta (margin beta) / ((nH : ℝ) + 1)) ^ nH) ≤
        Measure.real muH (Region beta) := by
  rw [p4Q2PZ37AIK_elementaryNegativeHaarFloor_eq H beta hbeta]
  exact p4Q2PZ37AIJ_originalFullNegativeRegion_combinedMass H beta hbeta

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_sphereRadiusFraction_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_sphereRadiusFraction_of_nonpos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_sphereRadiusFraction_eq_quartic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius_rational
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_sphereRadiusFraction_pow
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIK_originalOneLinkBall_mass_ge_elementary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_originalSpatialBall_mass_ge_elementary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementarySourceVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementarySourceVarianceFloor_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementarySourceVarianceFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeMargin_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeMargin_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeMargin_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeMargin_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeBallRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeBallRadius_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeBallRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeBallRadius_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeHaarFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeHaarFloor_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeHaarFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeBall_fullMargin_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeBall_mass_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_originalTransfer_exists_elementaryNegativeHaarBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_originalFullNegativeRegion_elementaryMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_elementaryNegativeRegion_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIK_originalFullNegativeRegion_combinedMass
