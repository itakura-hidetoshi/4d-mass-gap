import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundarySignedResponseHaarPositiveV5_GT
import Mathlib.Tactic

/-!
# P4-Q2-GU: genuine ORIGINAL Wilson posterior L² mass of the physical
two-LEFT-boundary signed right-link response contrast

GT shows that the squared difference of the SAME two original FF signed
physical receivers, at the actual identity and pi-rotated left physical
boundaries and fixed updated right configuration, has positive SU(2)
reference-Haar mass whenever the true physical source's frozen Wilson
transfer is positive at the genuine SU(2) pi insertion.

Here integrate that SAME squared physical response difference under
the ACTUAL interacting original Wilson conditional posterior law
at the identity left boundary. This is *not* Haar masquerading as a
posterior measure: the law is the original vacuum-posterior
SpatialLinkConditionalMeasure from the finite physical one-slab Wilson
kernel and positive Perron vacuum.

Prove exact equality with a Haar reference integral weighted by the
genuine posterior density p_id. The original Wilson FK finite-volume
Harnack estimate gives p_id(g) >= exp(-16 beta) for ALL true link values.
Thus

  exp(-16 beta) * HaarSqMass <= TruePosteriorSqMass,

independent of H, e and right environment. Combining with GS/GT yields
strict positivity on the original interacting Wilson conditional
posterior, without assuming any Haar atom.

Specialize to the actual fine-right Krylov and left-three-mode physical
source combinations: fine beta(n+1) stays INSIDE source factors;
posterior, receiver and source transfer use frozen beta(n).

This is a true posterior expected SQUARE OF TWO RESPONSE ROW DIFFERENCES,
not the GI difference of two posterior expectations of ONE response
(Delta). No unjustified implication to GI detector injectivity, a
volume-uniform signed source frame, H1-C3 closure or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 730000

local instance p4Q2GUPosterior_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GUPosterior_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GUPosterior_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GUPosterior_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GUPosterior_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μ" => normalizedCompactHaar Gauge
local notation "Nu" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
    H 2 (by norm_num) beta hbeta
local notation "P0" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H)

/-- The conditional posterior is the ACTUAL original interacting Wilson
measure on this same right physical background and link. -/
noncomputable def p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
    (f : Phys) (right : Cfg) (e : Link) : ℝ :=
  ∫ g : Gauge,
    (p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
      H beta hbeta f right e g) ^ 2
    ∂Nu (originalWilsonExplicitIdentityBoundary H) right e

/-- The continuous actual physical receiver difference has integrable
square under the genuine original interacting Wilson conditional posterior
probability measure, not just under the outer Haar reference measure. -/
theorem p4Q2GU_originalPhysicalTwoBoundaryContrastPosterior_integrable
    (f : Phys) (right : Cfg) (e : Link) :
    Integrable (fun g : Gauge =>
      (p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
        H beta hbeta f right e g) ^ 2)
      (Nu (originalWilsonExplicitIdentityBoundary H) right e) := by
  haveI : IsProbabilityMeasure
      (Nu (originalWilsonExplicitIdentityBoundary H) right e) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  exact ((p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_continuous
    H beta hbeta f right e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Integrating the original physical response-square under the true
interacting posterior is EXACTLY integrating that response-square against
its actual normalized Wilson density relative to Haar.
This is an identity of genuine measures, not a posterior replacement. -/
theorem p4Q2GU_originalPhysicalContrastPosteriorMass_eq_weightedHaar
    (f : Phys) (right : Cfg) (e : Link) :
    p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        H beta hbeta f right e =
      ∫ g : Gauge,
        P0 right e g *
          (p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
            H beta hbeta f right e g) ^ 2 ∂μ := by
  let ν : Measure Gauge := normalizedCompactHaar Gauge
  let ℓ : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  let D := p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
    H beta hbeta f right e
  change (∫ g : Gauge, (D g) ^ 2 ∂ν.tilted ℓ) =
    ∫ g : Gauge, continuousNormalizedExp ν ℓ g * (D g) ^ 2 ∂ν
  rw [integral_tilted]
  rfl

theorem p4Q2GU_originalPhysicalContrastPosteriorMass_nonneg
    (f : Phys) (right : Cfg) (e : Link) :
    0 ≤ p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      H beta hbeta f right e := by
  unfold p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
  exact integral_nonneg (fun g => sq_nonneg _)

/-- The ACTUAL interacting Wilson posterior squared physical source
response contrast dominates exp(-16 beta) times its compact Haar
reference mass, with NO finite volume, physical-link-count or source
coordinate-frame multiplier inserted. -/
theorem p4Q2GU_originalPhysicalContrastPosteriorMass_ge_Haar
    (f : Phys) (right : Cfg) (e : Link) :
    Real.exp (-16 * beta) *
        p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
          H beta hbeta f right e ≤
      p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        H beta hbeta f right e := by
  let D := p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
    H beta hbeta f right e
  let P : Gauge → ℝ := P0 right e
  let ν : Measure Gauge := normalizedCompactHaar Gauge
  let ℓ : Gauge → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  have hContD : Continuous D :=
    p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_continuous
      H beta hbeta f right e
  have hContL : Continuous ℓ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
  have hContP : Continuous P := by
    change Continuous (continuousNormalizedExp ν ℓ)
    exact continuous_continuousNormalizedExp ν ℓ hContL
  have hIntSq : Integrable (fun g : Gauge => (D g) ^ 2) μ :=
    (hContD.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntWeighted : Integrable (fun g : Gauge => P g * (D g) ^ 2) μ :=
    (hContP.mul (hContD.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLower (g : Gauge) : Real.exp (-16 * beta) ≤ P g :=
    (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H)
      right e g).1
  rw [p4Q2GU_originalPhysicalContrastPosteriorMass_eq_weightedHaar]
  change Real.exp (-16 * beta) * (∫ g, (D g) ^ 2 ∂μ) ≤
    ∫ g, P g * (D g) ^ 2 ∂μ
  calc
    Real.exp (-16 * beta) * (∫ g, (D g) ^ 2 ∂μ) =
        ∫ g, Real.exp (-16 * beta) * (D g) ^ 2 ∂μ := by
      rw [integral_const_mul]
    _ ≤ ∫ g, P g * (D g) ^ 2 ∂μ := by
      apply integral_mono (hIntSq.const_mul _) hIntWeighted
      intro g
      exact mul_le_mul_of_nonneg_right (hLower g) (sq_nonneg _)

/-- GS/GT's true physical transfer witness now produces positive
squared signed two-boundary response mass under the ACTUAL interacting
identity-left Wilson conditional posterior, not just Haar. -/
theorem p4Q2GU_originalPhysicalContrastPosteriorMass_pos_of_transfer
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      H beta hbeta f right e := by
  have hHaar : 0 <
      p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
        H beta hbeta f right e :=
    p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
      H beta hbeta hpos f right e hTransfer
  have hBound :=
    p4Q2GU_originalPhysicalContrastPosteriorMass_ge_Haar
      H beta hbeta f right e
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hHaar) hBound

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The SAME actual fine right Krylov signed physical source has strictly
positive two-LEFT-boundary response-square expectation under the true
FROZEN beta(n) interacting Wilson conditional law whenever its genuine
original frozen transfer at the pi update is positive. -/
theorem p4Q2GU_actualFineRightKrylov_PosteriorMass_pos_of_transfer
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e := by
  have hT : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (↑(∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)))
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hTransfer
  exact p4Q2GU_originalPhysicalContrastPosteriorMass_pos_of_transfer
    Hn (beta n) (hbeta n) hFrozen _ right e hT

/-- The exact actual fine left-three-mode signed source inherits
strict posterior L² separation without identifying fine beta(n+1)
with the frozen beta(n) of the interacting conditional law. -/
theorem p4Q2GU_actualFineLeftThreeMode_PosteriorMass_pos_of_transfer
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ k : Fin 3, a k • LeftFactor n r k)
      right e := by
  exact p4Q2GU_originalPhysicalContrastPosteriorMass_pos_of_transfer
    Hn (beta n) (hbeta n) hFrozen _ right e hTransfer

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalTwoBoundaryContrastPosterior_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalContrastPosteriorMass_eq_weightedHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalContrastPosteriorMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalContrastPosteriorMass_ge_Haar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalContrastPosteriorMass_pos_of_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_actualFineRightKrylov_PosteriorMass_pos_of_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_actualFineLeftThreeMode_PosteriorMass_pos_of_transfer
