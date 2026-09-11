import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAEFiberMass
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitJointAEMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance specialUnitaryGroupIsTopologicalGroupForSplitProductMass (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance specialUnitaryGroupCompactSpaceForSplitProductMass (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance specialUnitaryGroupSecondCountableTopologyForSplitProductMass (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance specialUnitaryGroupMeasurableSpaceForSplitProductMass (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance specialUnitaryGroupBorelSpaceForSplitProductMass (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance periodicHypercubicEvenSpatialSliceLinkFintypeForSplitProductMass (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForSplitProductMass
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- The positive finite ground-state singleton-target fiber-mass statement can
be promoted from its canonical double-a.e. form to a genuine product-measure
a.e. statement on `(left, retained)`.

The promotion is not a bare reinterpretation of nested almost-everywhere
quantifiers.  Joint split-density a.e.-measurability first gives an
a.e.-measurable literal mass function.  We pass to its measurable `mk`
representative, use `Measure.ae_prod_iff_ae_ae` only for the measurable
positive-finite predicate of that representative, and then transport the
result back to the literal mass function by a.e. equality. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top_prod
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
      0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta ctx.1 target ctx.2 ∧
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta ctx.1 target ctx.2 < ∞ := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let Z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ENNReal :=
    fun ctx =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
        H N hN beta hbeta ctx.1 target ctx.2
  have hw :
      AEMeasurable
        (fun z :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
                  Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
              (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta z.1.1 target (z.2, z.1.2))
        ((μ.prod μOff).prod μTarget) := by
    simpa [μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
        H N hN beta hbeta target)
  have hZ : AEMeasurable Z (μ.prod μOff) := by
    simpa [Z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass]
      using hw.lintegral_prod_right'
  let Z' := hZ.mk Z
  have hZ'm : Measurable Z' := by
    exact hZ.measurable_mk
  have hZZ' : Z =ᵐ[μ.prod μOff] Z' :=
    hZ.ae_eq_mk
  have hGoodDouble :
      ∀ᵐ left ∂μ, ∀ᵐ retained ∂μOff,
        0 < Z (left, retained) ∧ Z (left, retained) < ∞ := by
    simpa [μ, μOff, Z] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top
        H N hN beta hbeta target)
  have hEqDouble :
      ∀ᵐ left ∂μ, ∀ᵐ retained ∂μOff,
        Z (left, retained) = Z' (left, retained) := by
    simpa using (Measure.ae_ae_of_ae_prod hZZ')
  have hGoodPrimeDouble :
      ∀ᵐ left ∂μ, ∀ᵐ retained ∂μOff,
        0 < Z' (left, retained) ∧ Z' (left, retained) < ∞ := by
    filter_upwards [hGoodDouble, hEqDouble] with left hgoodLeft heqLeft
    filter_upwards [hgoodLeft, heqLeft] with retained hgood heq
    simpa [heq] using hgood
  have hGoodPrimeMeas :
      MeasurableSet {ctx | 0 < Z' ctx ∧ Z' ctx < ∞} :=
    (measurableSet_lt measurable_const hZ'm).inter
      (measurableSet_lt hZ'm measurable_const)
  have hGoodPrimeProd :
      ∀ᵐ ctx ∂(μ.prod μOff), 0 < Z' ctx ∧ Z' ctx < ∞ :=
    (Measure.ae_prod_iff_ae_ae hGoodPrimeMeas).2 hGoodPrimeDouble
  have hGoodProd :
      ∀ᵐ ctx ∂(μ.prod μOff), 0 < Z ctx ∧ Z ctx < ∞ := by
    filter_upwards [hGoodPrimeProd, hZZ'] with ctx hgood heq
    simpa [heq] using hgood
  simpa [μ, μOff, Z] using hGoodProd

/-- Product-a.e. positive finite mass in exactly the `doobWeightMass` form
required by the generic measurable Markov-kernel theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetDoobWeightMass_ae_pos_lt_top_prod
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
      0 < doobWeightMass
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
          (fun targetCfg =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
              H N hN beta hbeta ctx.1 target (targetCfg, ctx.2)) ∧
        doobWeightMass
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
          (fun targetCfg =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
              H N hN beta hbeta ctx.1 target (targetCfg, ctx.2)) < ∞ := by
  simpa [doobWeightMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top_prod
        H N hN beta hbeta target)

end

end MathlibAnalytic
end MGAP4D