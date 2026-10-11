import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCommutationFromRetainedMeasurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-CU: genuine pair-Haar independent two-link Haar averaging commutes

CT reduced full-L² coordinate-projection commutation to actual Fubini
retention of each other coordinate sigma-algebra. Before claiming
commutation on L² quotient vectors, establish its exact LITERAL
coordinate-Haar integral identity on the actual finite original left
and right SU(N) pair-Haar configuration.

A bounded strongly measurable original observable has well-defined
double Haar integrals on ANY two distinct physical coordinate links.
These integrals commute BY FINITE-PRODUCT FUBINI with exactly the same
pointwise observable and Haar law; the function updates commute
because the physical links are distinct.

The first theorem is generic for a homogeneous independent probability
product, and the second theorem transports it to the existing
measure-preserving original left/right pair-Haar coordinate equivalence.
No synthetic Wilson measure, no beta-zero assumption and no exceptional
L² representative point evaluations enter the physical theorem.

The result is concrete Haar *function* averaging commutation.
Identifying its bounded-core action with CR's L² orthogonal projection
and extending by dense-range continuity is the NEXT proof obligation.
Do not mistake this exact Fubini result for already-proved full-L²
commutation, positive Wilson reverse coercivity, volume-uniform gap
or continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

/-- Literal Haar average of one finite homogeneous-product coordinate,
on actual pointwise observables. Unlike a conditional-expectation
projection, this operator does not quotient by almost-everywhere equality. -/
noncomputable def p4Q2CU_finiteProductCoordinateHaarMean
    {ι G : Type*} [DecidableEq ι] [MeasurableSpace G]
    (μ : Measure G) (i : ι) (F : (ι → G) → ℝ) (z : ι → G) : ℝ :=
  ∫ u, F (Function.update z i u) ∂μ

/-- EXACT independent Haar two-coordinate Fubini identity for bounded
strongly measurable observables, at any fixed configuration z.
Neither coordinate requires a conditional-law identification. -/
theorem p4Q2CU_finiteProductCoordinateHaarMean_commute
    {ι G : Type*} [DecidableEq ι] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j)
    (F : (ι → G) → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) (z : ι → G) :
    p4Q2CU_finiteProductCoordinateHaarMean μ i
        (p4Q2CU_finiteProductCoordinateHaarMean μ j F) z =
      p4Q2CU_finiteProductCoordinateHaarMean μ j
        (p4Q2CU_finiteProductCoordinateHaarMean μ i F) z := by
  letI : IsProbabilityMeasure (μ.prod μ) := by infer_instance
  have hup :
      Measurable (fun p : G × G =>
        Function.update (Function.update z i p.1) j p.2) := by
    fun_prop
  have hstrong : StronglyMeasurable (fun p : G × G =>
      F (Function.update (Function.update z i p.1) j p.2)) :=
    hF.comp_measurable hup
  have hbounded : ∀ p : G × G,
      ‖F (Function.update (Function.update z i p.1) j p.2)‖ ≤ M :=
    fun p => hM _
  have hint : Integrable
      (fun p : G × G =>
        F (Function.update (Function.update z i p.1) j p.2)) (μ.prod μ) :=
    Integrable.of_bound hstrong.aestronglyMeasurable M
      (Filter.Eventually.of_forall hbounded)
  change
    (∫ u, ∫ v, F (Function.update (Function.update z i u) j v) ∂μ ∂μ) =
      (∫ v, ∫ u, F (Function.update (Function.update z j v) i u) ∂μ ∂μ)
  calc
    (∫ u, ∫ v,
        F (Function.update (Function.update z i u) j v) ∂μ ∂μ) =
        ∫ v, ∫ u,
          F (Function.update (Function.update z i u) j v) ∂μ ∂μ :=
      integral_integral_swap hint
    _ = (∫ v, ∫ u,
          F (Function.update (Function.update z j v) i u) ∂μ ∂μ) := by
      simp_rw [Function.update_comm hij]

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
local notation "μH" => normalizedCompactHaar G

/-- Average the literal original physical left/right joint observable
over ONE selected actual Haar coordinate via the existing canonical
joint coordinate measurable equivalence. -/
noncomputable def p4Q2CU_actualPairHaarCoordinateMean
    (i : I) (F : Joint → ℝ) (z : Joint) : ℝ :=
  let e :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  ∫ u : G, F (e.symm (Function.update (e z) i u)) ∂μH

/-- Physical endpoint/link version of exact independent coordinate
Fubini commutation, for EVERY bounded strongly measurable observable
on the actual pair-Haar left/right spatial configuration carrier. -/
theorem p4Q2CU_actualPairHaarCoordinateMean_commute
    (i j : I) (hij : i ≠ j)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) (z : Joint) :
    p4Q2CU_actualPairHaarCoordinateMean H N i
        (p4Q2CU_actualPairHaarCoordinateMean H N j F) z =
      p4Q2CU_actualPairHaarCoordinateMean H N j
        (p4Q2CU_actualPairHaarCoordinateMean H N i F) z := by
  classical
  let e :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  let F' : (I → G) → ℝ := fun w => F (e.symm w)
  have hF' : StronglyMeasurable F' :=
    hF.comp_measurable e.symm.measurable
  have hbound : ∀ w : I → G, ‖F' w‖ ≤ M :=
    fun w => hM (e.symm w)
  have h := p4Q2CU_finiteProductCoordinateHaarMean_commute
    μH i j hij F' hF' M hbound (e z)
  simpa [p4Q2CU_actualPairHaarCoordinateMean,
    p4Q2CU_finiteProductCoordinateHaarMean, F', e,
    Function.comp_def] using h

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
