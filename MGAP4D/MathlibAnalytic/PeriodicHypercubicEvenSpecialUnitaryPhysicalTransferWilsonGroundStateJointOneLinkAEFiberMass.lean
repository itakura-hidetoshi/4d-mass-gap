import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAEFiberMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Keep the singleton target subtype on the exact `Fintype` presentation used
by the canonical Haar coordinate split. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForAEFiberMass
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- Total mass of the actual ground-state right-joint density along the
singleton target factor after the canonical `target × off-target` Haar split.

This is an unnormalized coordinate fiber mass only.  It is not yet identified
with a regular conditional distribution or with the Wilson one-link Doob law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ENNReal :=
  ∫⁻ targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
      H N hN beta hbeta left target (targetCfg, retained)
    ∂(Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- For Haar-a.e. left boundary and Haar-a.e. retained off-target context, the
actual ground-state target-link split fiber has strictly positive finite mass.

The proof keeps both exceptional sets.  Finiteness comes from Fubini applied to
the globally integrable normalized real joint weight after the canonical
measure-preserving split.  Positivity comes from transporting the global a.e.
strict positivity through the same split and then applying Fubini in the
opposite coordinate order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        0 <
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
              H N hN beta hbeta left target retained ∧
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
              H N hN beta hbeta left target retained < ∞ := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  haveI : IsProbabilityMeasure μTarget := by
    dsimp [μTarget]
    infer_instance
  have hsplit : MeasurePreserving split μ (μTarget.prod μOff) := by
    simpa [split, μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
        H N target)
  have hsplitInv : MeasurePreserving split.symm (μTarget.prod μOff) μ :=
    hsplit.symm
  have hglobalInt :
      Integrable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta)
        (μ.prod μ) := by
    simpa [μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta)
  have hleftInt :
      ∀ᵐ left ∂μ,
        Integrable
          (fun right =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
              H N hN beta hbeta (left, right)) μ :=
    hglobalInt.prod_right_ae
  have hglobalPos :
      ∀ᵐ z ∂(μ.prod μ),
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta z := by
    simpa [μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
        H N hN beta hbeta)
  have hleftPos :
      ∀ᵐ left ∂μ,
        ∀ᵐ right ∂μ,
          0 <
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
              H N hN beta hbeta (left, right) :=
    Measure.ae_ae_of_ae_prod hglobalPos
  have hfiberMeas :
      ∀ᵐ left ∂μ,
        ∀ᵐ retained ∂μOff,
          AEMeasurable
            (fun targetCfg :
                PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                  Matrix.specialUnitaryGroup (Fin N) ℂ =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
                H N hN beta hbeta left target (targetCfg, retained)) μTarget := by
    simpa [μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_ae_targetFiber
        H N hN beta hbeta target)
  filter_upwards [hleftInt, hleftPos, hfiberMeas] with left hleftInt' hleftPos' hleftMeas
  have hsplitInt :
      Integrable
        (fun z =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta (left, split.symm z))
        (μTarget.prod μOff) := by
    have hcomp :=
      (hsplitInv.integrable_comp_emb split.symm.measurableEmbedding).2 hleftInt'
    simpa [Function.comp_def] using hcomp
  have hfiberInt :
      ∀ᵐ retained ∂μOff,
        Integrable
          (fun targetCfg =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
              H N hN beta hbeta (left, split.symm (targetCfg, retained))) μTarget :=
    hsplitInt.prod_left_ae
  have hsplitPos :
      ∀ᵐ z ∂(μTarget.prod μOff),
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta (left, split.symm z) :=
    hsplitInv.quasiMeasurePreserving.ae hleftPos'
  have hsplitPosSwap :
      ∀ᵐ z ∂(μOff.prod μTarget),
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta (left, split.symm z.swap) := by
    exact Measure.measurePreserving_swap.quasiMeasurePreserving.ae hsplitPos
  have hfiberPosReal :
      ∀ᵐ retained ∂μOff,
        ∀ᵐ targetCfg ∂μTarget,
          0 <
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
              H N hN beta hbeta (left, split.symm (targetCfg, retained)) := by
    simpa [Prod.swap] using (Measure.ae_ae_of_ae_prod hsplitPosSwap)
  filter_upwards [hfiberInt, hfiberPosReal, hleftMeas] with retained hint hposReal hmeas
  constructor
  · change 0 < ∫⁻ targetCfg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta left target (targetCfg, retained) ∂μTarget
    have hposDensity :
        ∀ᵐ targetCfg ∂μTarget,
          0 <
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
              H N hN beta hbeta left target (targetCfg, retained) := by
      filter_upwards [hposReal] with targetCfg htarget
      simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity, split] using
        (ENNReal.ofReal_pos.2 htarget)
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hzeroFiber :
        (fun targetCfg =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta left target (targetCfg, retained)) =ᵐ[μTarget] 0 :=
      (lintegral_eq_zero_iff' hmeas).1 hzero
    have hfalse : ∀ᵐ targetCfg ∂μTarget, False := by
      filter_upwards [hposDensity, hzeroFiber] with targetCfg htarget htargetZero
      exact (ne_of_gt htarget) htargetZero
    exact (hfalse.exists).elim fun _ h => h
  · change (∫⁻ targetCfg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta left target (targetCfg, retained) ∂μTarget) < ∞
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity, split] using
      hint.lintegral_lt_top

end

end MathlibAnalytic
end MGAP4D
