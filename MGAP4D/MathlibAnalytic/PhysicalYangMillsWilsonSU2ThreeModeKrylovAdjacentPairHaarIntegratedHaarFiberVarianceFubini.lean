import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSplitUpdateMeanIdentification
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# P4-Q2-DH: physical Haar fiber variance is a genuine joint centered square

CV/CY/CZ/DA identified bounded conditional Haar coordinate averages with
the TRUE physical pair-Haar Hilbert-L² projection. DC proved the genuine
reference finite-coordinate Poincare inequality. CP and DG provide a
positive original Wilson finite-volume link Haar-reference mass floor.

The missing elementary quantitative bridge is Fubini's equality between
the integral over outer contexts of each actual Haar fiber variance and
the one full-joint Haar integral of the squared difference from its
literal coordinate Haar mean. We prove it first on a genuine product
measure, then transport it across the EXISTING exact original joint
left/right SU(N) pair-Haar measurable equivalence from CY.

The result uses the ORIGINAL pair-Haar law and actual normalized
compact SU(N) Haar coordinate, not a synthetic interacting Wilson law.
Further identification with the full Hilbert-L² residual norm and
all-12-color Wilson lower coercivity remains to be established.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

/-- On any genuine product of sigma-finite measures, the integrated
one-fiber extended Haar variance is EXACTLY the joint integral of the
squared deviation from its literal fiber mean. This is the actual
nonnegative Fubini formula (no a.e. quotient point evaluations). -/
theorem p4Q2DH_productIntegratedFiberVariance_eq_jointCenteredLIntegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (F : α × β → ℝ) (hF : StronglyMeasurable F) :
    (∫⁻ a, evariance (fun b : β => F (a, b)) ν ∂μ) =
      ∫⁻ z : α × β,
        ENNReal.ofReal ((F z - ∫ b : β, F (z.1, b) ∂ν) ^ 2)
        ∂(μ.prod ν) := by
  have hmean : StronglyMeasurable
      (fun a : α => ∫ b : β, F (a, b) ∂ν) :=
    hF.integral_prod_right'
  have hdiff : StronglyMeasurable
      (fun z : α × β => F z - ∫ b : β, F (z.1, b) ∂ν) :=
    hF.sub (hmean.comp_measurable measurable_fst)
  have hMeas : Measurable
      (fun z : α × β =>
        ENNReal.ofReal ((F z - ∫ b : β, F (z.1, b) ∂ν) ^ 2)) :=
    (hdiff.measurable.pow_const 2).ennreal_ofReal
  calc
    (∫⁻ a, evariance (fun b : β => F (a, b)) ν ∂μ) =
        ∫⁻ a, ∫⁻ b : β,
          ENNReal.ofReal ((F (a, b) - ∫ t : β, F (a, t) ∂ν) ^ 2)
          ∂ν ∂μ := by
            apply lintegral_congr
            intro a
            exact evariance_eq_lintegral_ofReal
              (fun b : β => F (a, b)) ν
    _ = ∫⁻ z : α × β,
        ENNReal.ofReal ((F z - ∫ b : β, F (z.1, b) ∂ν) ^ 2)
        ∂(μ.prod ν) :=
          (lintegral_prod _ hMeas.aemeasurable).symm

/-- Transport the exact variance-Fubini identity along any honest
measure-preserving measurable equivalence to a TRUE product law, with
no change to the original probability space or exceptional fibers. -/
theorem p4Q2DH_measurePreservingEquiv_integratedFiberVariance
    {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (ω : Measure Ω) (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (e : Ω ≃ᵐ (α × β))
    (he : MeasurePreserving e ω (μ.prod ν))
    (F : Ω → ℝ) (hF : StronglyMeasurable F) :
    (∫⁻ a, evariance (fun b : β => F (e.symm (a, b))) ν ∂μ) =
      ∫⁻ z : Ω,
        ENNReal.ofReal
          ((F z - ∫ b : β, F (e.symm ((e z).1, b)) ∂ν) ^ 2)
        ∂ω := by
  have hprod : StronglyMeasurable
      (fun p : α × β => F (e.symm p)) :=
    hF.comp_measurable e.symm.measurable
  have hFubini :=
    p4Q2DH_productIntegratedFiberVariance_eq_jointCenteredLIntegral
      μ ν (fun p : α × β => F (e.symm p)) hprod
  have hMap := lintegral_map_equiv
      (μ := ω)
      (fun p : α × β =>
        ENNReal.ofReal
          ((F (e.symm p) -
            ∫ b : β, F (e.symm (p.1, b)) ∂ν) ^ 2))
      e
  rw [he.map_eq] at hMap
  exact hFubini.trans (by
    simpa only [e.symm_apply_apply] using hMap)

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

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muH" => normalizedCompactHaar G
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N

/-- For EVERY literal original left/right physical link, the actual
off-link product Haar integral of its SU(N) fiber variance is the
full ORIGINAL spatial pair-Haar integral of the squared deviation
from the genuine single-link Haar mean. -/
theorem p4Q2DH_actualPairHaarIntegratedFiberVariance_eq_jointSquare
    (i : I) (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    (∫⁻ a : {j : I // j ≠ i} → G,
      evariance (fun u : G =>
        F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm (a, u)))
        muH
      ∂(Measure.pi (fun _ : {j : I // j ≠ i} => muH))) =
      ∫⁻ z : Joint,
        ENNReal.ofReal
          ((F z - ∫ u : G,
            F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm
              (((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i) z).1, u))
            ∂muH) ^ 2)
        ∂muPair := by
  classical
  let μOff : Measure ({j : I // j ≠ i} → G) :=
    Measure.pi (fun _ : {j : I // j ≠ i} => muH)
  let e := p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i
  have he : MeasurePreserving e muPair (μOff.prod muH) := by
    simpa [e, μOff] using
      (p4Q2CY_actualPairHaarOffLinkSingleHaar_measurePreserving H N i)
  simpa [μOff, e] using
    (p4Q2DH_measurePreservingEquiv_integratedFiberVariance
      muPair μOff muH e he F hF)

/-- Replacing the transported split-fiber mean by DA's literal
original Function.update Haar mean gives precisely the same physical
pair-Haar joint squared-deviation energy. -/
theorem p4Q2DH_actualPairHaarIntegratedFiberVariance_eq_CUmeanSquare
    (i : I) (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    (∫⁻ a : {j : I // j ≠ i} → G,
      evariance (fun u : G =>
        F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm (a, u)))
        muH
      ∂(Measure.pi (fun _ : {j : I // j ≠ i} => muH))) =
      ∫⁻ z : Joint,
        ENNReal.ofReal
          ((F z - p4Q2CU_actualPairHaarCoordinateMean H N i F z) ^ 2)
        ∂muPair := by
  simpa only [p4Q2DA_actualPairHaar_splitFiberMean_eq_CU] using
    (p4Q2DH_actualPairHaarIntegratedFiberVariance_eq_jointSquare
      H N i F hF)

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
