import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PhysicalReferenceStrictPositive
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalContinuousDensityFiniteVolumeSandwich
import Mathlib.Tactic

/-!
# P4-Q2-EJ: original Wilson mass-weighted Haar off-target fiber vanishing

For the SAME genuine SU(2) original two-boundary gauge-invariant relative-link
Wilson-energy observable certified in ED-EI, EF proves pointwise invariance
under ANY off-target joint left/right link coordinate replacement. We insert
that exact identity into the actual original continuous Wilson-Perron
physical joint density and the literal normalized SU(2) Haar resampling
integral. This proves off-target original Wilson mass-weighted Haar fiber
energy vanishes, despite the physical Wilson density being nonconstant.

This is the ACTUAL original unnormalized physical Wilson-Haar REFERENCE
one-coordinate squared-difference integrand, not an interacting Wilson
conditional-expectation projection or an independent new probability measure.
Selected left/right coordinate contributions can remain positive; EI proves
the full actual original Wilson reference and full-joint Riesz energies
strictly positive. Uniform H/spacing bounds and signed fine/frozen Krylov
remain open. No sorry/admit/new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualOriginalWilsonOffTarget

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "I" => PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "E" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H 2
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "w" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num) beta hbeta

/-- Genuine physical Wilson-Perron-density weighted off-target Haar
resampling squared difference is IDENTICALLY zero for each background
pair configuration and each actual SU(2) replacement value. -/
theorem p4Q2EJ_offTarget_originalWilsonMassWeightedDifference_zero
    (e : Link) (i : I) (hiL : i ≠ Sum.inl e)
    (hiR : i ≠ Sum.inr e) (z : Joint) (u : G) :
    ENNReal.ofReal (w z) *
      ENNReal.ofReal
        ((F e
          ((periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H 2).symm
            (Function.update (E z) i u)) - F e z) ^ 2) = 0 := by
  have hEq :=
    p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_update_eq
      H e i hiL hiR z u
  rw [hEq, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

/-- Literal true SU(2) Haar inner fiber integral vanishes for EVERY
off-target original left/right joint coordinate. It retains the
ACTUAL original Wilson-Perron mass factor at the base configuration. -/
theorem p4Q2EJ_offTarget_originalWilsonMassWeightedHaarFiber_zero
    (e : Link) (i : I) (hiL : i ≠ Sum.inl e)
    (hiR : i ≠ Sum.inr e) (z : Joint) :
    (∫⁻ u : G,
      ENNReal.ofReal (w z) *
        ENNReal.ofReal
          ((F e
            ((periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H 2).symm
              (Function.update (E z) i u)) - F e z) ^ 2)
      ∂normalizedCompactHaar G) = 0 := by
  have hZero :
      (fun u : G =>
        ENNReal.ofReal (w z) *
          ENNReal.ofReal
            ((F e
              ((periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H 2).symm
                (Function.update (E z) i u)) - F e z) ^ 2)) =
          (fun _ : G => (0 : ENNReal)) := by
    funext u
    exact p4Q2EJ_offTarget_originalWilsonMassWeightedDifference_zero
      H beta hbeta e i hiL hiR z u
  rw [hZero]
  simp

end ActualOriginalWilsonOffTarget
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EJ_offTarget_originalWilsonMassWeightedDifference_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2EJ_offTarget_originalWilsonMassWeightedHaarFiber_zero
