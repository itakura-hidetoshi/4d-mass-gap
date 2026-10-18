import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointPosteriorHalfDensityDescentV5_GQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNormalizedPosteriorTemporalLogCrossingV5_FR
import Mathlib.Tactic

/-!
# P4-Q2-KG — exact four-corner cross ratio of the ORIGINAL Wilson joint density

GQ identifies the *original* strictly positive normalized Perron/Wilson
joint density's fiber dependence with the *original* genuinely interacting
one-link posterior. FR proves the four-corner log difference of these
original normalized posteriors equals precisely the crossing-plaquette
Wilson energy, with no vacuum or partition residues.

Here we transfer that exact four-corner identity back to the literal
original physical joint density, for arbitrary left boundaries L₁,L₂,
right background R, actual link e, and actual SU(2) insertions g,h:

  rho(L₁,R_g) rho(L₂,R_h)
    = exp(-b * Delta_temporal) rho(L₁,R_h) rho(L₂,R_g),

  Delta_temporal =
    [E((L₁e)^(-1)g)-E((L₁e)^(-1)h)]
      - [E((L₂e)^(-1)g)-E((L₂e)^(-1)h)].

All genuine Perron vacuum, spatial half weights, and joint normalization
have cancelled by *proved* identities. No independent-Haar posterior,
artificial source, new axiom/sorry/admit, H1-C3, or continuum mass gap.
This is a pointwise finite-Wilson structural identity, not yet
single-link exponential-convolution injectivity or GI nonzero detection.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num)
local notation "post" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num)

/-- At any actual left/right/link fiber, the log increment of the true
joint density is exactly that of the original normalized interacting
posterior. The left Perron and local partition factors cancel. -/
theorem p4Q2KG_originalJointLogFiberIncrement_eq_originalPosterior
    (b : ℝ) (hb : 0 ≤ b) (left right : Cfg) (e : Link)
    (g h : Gauge) :
    Real.log (rho b hb (left, Function.update right e g)) -
        Real.log (rho b hb (left, Function.update right e h)) =
      Real.log (post b hb left right e g) -
        Real.log (post b hb left right e h) := by
  have hRg : 0 < rho b hb (left, Function.update right e g) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left, Function.update right e g)
  have hRh : 0 < rho b hb (left, Function.update right e h) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left, Function.update right e h)
  have hPg : 0 < post b hb left right e g :=
    p4Q2GQ_originalPosteriorDensity_pos H b hb left right e g
  have hPh : 0 < post b hb left right e h :=
    p4Q2GQ_originalPosteriorDensity_pos H b hb left right e h
  have hCross :=
    p4Q2GQ_originalJointPosteriorFiber_cross H b hb left right e g h
  have hLog := congrArg Real.log hCross
  rw [Real.log_mul hRg.ne' hPh.ne',
    Real.log_mul hRh.ne' hPg.ne'] at hLog
  linarith

/-- The *literal* original physical Perron/Wilson joint density obeys
the exact finite-volume SU(2) temporal Wilson four-corner LOG identity,
for arbitrary actual left configurations, without posterior replacement. -/
theorem p4Q2KG_originalJointLogFourCorner_eq_temporalWilson
    (b : ℝ) (hb : 0 ≤ b)
    (left₁ left₂ right : Cfg) (e : Link) (g h : Gauge) :
    (Real.log (rho b hb (left₁, Function.update right e g)) -
      Real.log (rho b hb (left₁, Function.update right e h))) -
    (Real.log (rho b hb (left₂, Function.update right e g)) -
      Real.log (rho b hb (left₂, Function.update right e h))) =
      -b *
        ((specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * h)) -
          (specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * h))) := by
  rw [p4Q2KG_originalJointLogFiberIncrement_eq_originalPosterior
        H b hb left₁ right e g h,
      p4Q2KG_originalJointLogFiberIncrement_eq_originalPosterior
        H b hb left₂ right e g h]
  exact p4Q2FR_originalWilsonNormalizedPosteriorLogCrossing_eq_temporalEnergy
    H 2 (by norm_num) b hb left₁ left₂ right e g h

/-- Original Perron/Wilson joint density's four-corner MULTIPLICATIVE
cross ratio. Every vacuum and normalization factor has disappeared by
the proved GQ/FR log identities, and the remaining factor is the
ACTUAL one-link temporal SU(2) Wilson plaquette exponential. -/
theorem p4Q2KG_originalJointDensityFourCorner_eq_temporalExp
    (b : ℝ) (hb : 0 ≤ b)
    (left₁ left₂ right : Cfg) (e : Link) (g h : Gauge) :
    rho b hb (left₁, Function.update right e g) *
      rho b hb (left₂, Function.update right e h) =
      Real.exp (-b *
        ((specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * h)) -
          (specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * h)))) *
        (rho b hb (left₁, Function.update right e h) *
          rho b hb (left₂, Function.update right e g)) := by
  let Bg := Function.update right e g
  let Bh := Function.update right e h
  let r11 : ℝ := rho b hb (left₁, Bg)
  let r12 : ℝ := rho b hb (left₁, Bh)
  let r21 : ℝ := rho b hb (left₂, Bg)
  let r22 : ℝ := rho b hb (left₂, Bh)
  let d : ℝ :=
    (specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy 2 ((left₁ e)⁻¹ * h)) -
      (specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy 2 ((left₂ e)⁻¹ * h))
  have h11 : 0 < r11 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₁, Bg)
  have h12 : 0 < r12 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₁, Bh)
  have h21 : 0 < r21 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₂, Bg)
  have h22 : 0 < r22 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb (left₂, Bh)
  have hFour :=
    p4Q2KG_originalJointLogFourCorner_eq_temporalWilson
      H b hb left₁ left₂ right e g h
  change (Real.log r11 - Real.log r12) -
    (Real.log r21 - Real.log r22) = -b * d at hFour
  have hLog :
      Real.log (r11 * r22) - Real.log (r12 * r21) = -b * d := by
    rw [Real.log_mul h11.ne' h22.ne', Real.log_mul h12.ne' h21.ne']
    linarith [hFour]
  have hExp := congrArg Real.exp hLog
  rw [Real.exp_sub, Real.exp_log (mul_pos h11 h22),
    Real.exp_log (mul_pos h12 h21)] at hExp
  have hFactor : r11 * r22 = Real.exp (-b * d) * (r12 * r21) := by
    apply (div_eq_iff (mul_pos h12 h21).ne').mp hExp
  change r11 * r22 = Real.exp (-b * d) * (r12 * r21)
  exact hFactor

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KG_originalJointLogFiberIncrement_eq_originalPosterior
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KG_originalJointLogFourCorner_eq_temporalWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KG_originalJointDensityFourCorner_eq_temporalExp
