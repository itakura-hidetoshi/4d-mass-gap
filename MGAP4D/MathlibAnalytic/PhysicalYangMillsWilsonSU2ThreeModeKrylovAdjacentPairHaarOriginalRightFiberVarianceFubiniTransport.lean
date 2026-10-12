import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarIntegratedFiberVarianceHilbertDefect
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSingleLinkPairHaarFactorization
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# P4-Q2-DJ: original Wilson right-link Haar variance transported to the same pair-Haar law

DG established a single finite-volume positive mass floor for all twelve
genuine original Wilson link Haar reference energies. DH/DI identified
actual product Haar fiber variances with the off-coordinate orthogonal
projection defect on the original physical pair-Haar joint L².

The original Wilson right-link reference does not use CY's off-link Pi
presentation: it integrates over (left boundary × off-target right links)
using the original direct target-link reconstruction, with the actual
normalized SU(N) Haar group as the fiber. CJ has ALREADY certified that
this exact split is a measure-preserving measurable equivalence to the
SAME original left/right physical pair-Haar measure.

Here we apply DH's rigorous generic Fubini equality directly to CJ's
genuine Wilson reference fiber coordinates and show the global
squared-deviation identity about its actual retained Haar mean. The
next step is to identify that literal right Haar mean with CU's genuine
coordinate mean and therefore DI's CR projection defect; neither a
surrogate measure nor arbitrary evaluation at a fixed fiber is introduced.

No positive-beta Wilson projection commutation, uniform spectral gap,
or continuum Yang--Mills mass-gap claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

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

/-- Reuse the literal original physical right-link outer carrier.
The CJ-private abbreviation is intentionally not referenced across modules. -/
private abbrev p4Q2DJ_rightContext (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- The actual original split Haar outer law, definitionally equal to
CJ's certified outer law. -/
private noncomputable def p4Q2DJ_rightOuterHaar (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2DJ_rightContext H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

section ActualOriginalRightLink
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muH" => normalizedCompactHaar G
local notation "Ctx" => p4Q2DJ_rightContext H N
local notation "muOuter" => p4Q2DJ_rightOuterHaar H N
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- The exact original Wilson right-link split maps its TRUE original
Haar outer-context × target Haar product back to original pair Haar.
We retain this inverse presentation as a measure-preserving map,
not a new reference probability law. -/
theorem p4Q2DJ_actualWilsonRightLinkSplit_symm_measurePreserving
    (target : Link) :
    MeasurePreserving
      (p4Q2CJ_directLinkJointMeasurableEquiv H N target).symm
      muPair ((muOuter target).prod muH) :=
  (p4Q2CJ_directLinkJoint_measPreserving H N target).symm

/-- On the original Wilson right-link split, reconstructing the joint
observable from the actual direct Haar group coordinate gives the
original one-link concrete section pointwise. -/
theorem p4Q2DJ_actualRightLink_reconstructedSection
    (target : Link) (F : Joint → ℝ)
    (ctx : Ctx target) (u : G) :
    F (p4Q2CJ_directLinkJointMeasurableEquiv H N target (ctx, u)) =
      Section target F ctx.1 ctx.2 u := by
  rfl

/-- Exact genuine original Wilson RIGHT link Haar evariance Fubini:
integrating the actual SU(N) fiber variance against the true left-Haar
× right-off-target-Haar context equals a squared-deviation integral on
the original left/right spatial pair-Haar configuration space.
The center is obtained from the SAME direct original Wilson split;
it is not the Wilson interacting conditional mean. -/
theorem p4Q2DJ_originalRightLinkHaarFiberVariance_eq_pairHaarSplitMeanSquare
    (target : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    (∫⁻ ctx : Ctx target,
      evariance (Section target F ctx.1 ctx.2) muH
      ∂(muOuter target)) =
      ∫⁻ z : Joint, ENNReal.ofReal
        ((F z -
          ∫ u : G, F
            (p4Q2CJ_directLinkJointMeasurableEquiv H N target
              (((p4Q2CJ_directLinkJointMeasurableEquiv H N target).symm z).1, u))
            ∂muH) ^ 2)
        ∂muPair := by
  let e := (p4Q2CJ_directLinkJointMeasurableEquiv H N target).symm
  have he : MeasurePreserving e muPair ((muOuter target).prod muH) :=
    p4Q2DJ_actualWilsonRightLinkSplit_symm_measurePreserving H N target
  have h :=
    p4Q2DH_measurePreservingEquiv_integratedFiberVariance
      muPair (muOuter target) muH e he F hF
  simpa only [p4Q2DJ_actualRightLink_reconstructedSection] using h

end ActualOriginalRightLink
end

end MathlibAnalytic
end MGAP4D
