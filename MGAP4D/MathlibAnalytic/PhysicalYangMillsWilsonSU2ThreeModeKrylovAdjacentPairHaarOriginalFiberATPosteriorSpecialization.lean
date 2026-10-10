import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiberATPosteriorBridge
import Mathlib.Tactic

/-!
# P4-Q2-AW: specialize exact Doob normalization to the ORIGINAL Wilson slab

The raw link law is the precise AS normalized conditional Haar probability
from the actual Wilson one-slab kernel, not the full four-dimensional
Wilson heat-bath law. The physical weight is the canonical *continuous*
representative of the true physical transfer top vacuum, which coincides
Haar-a.e. with the original physical vacuum L² class.

Using the exact two-stage normalization identity of AW's generic module,
show the AT posterior equals one-step normalization of the PRODUCT of
the literal Wilson local factor and the true vacuum factor. Then use
AT's exact anchored joint weight factorization to identify the
same posterior with one-step normalization of the actual positive
one-link continuous physical ground-state JOINT density.

This specialization does NOT identify the old arbitrary L² quotient
pointwise on exceptional fixed fibers; AV handles that by correct AE
transport. No new axiom/sorry/admit/volume-uniform mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open ProbabilityTheory
open scoped ENNReal InnerProductSpace

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4AWGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AWCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AWSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AWMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AWBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AWLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Two-stage normalized true one-slab Wilson raw Haar plus canonical
physical-vacuum Doob posterior equals a single normalized Haar law with
the PRODUCT of the exact Wilson local factor and physical vacuum weight.
All required mass/integrability properties follow from the true finite-H
Wilson kernel and the previous AS/AT theorems. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabATPosteriorLaw_eq_HaarDoob_localWilson_mul_continuousVacuum
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
      H N hN beta hbeta left right target =
    doobWeightedMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (fun g =>
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta left right target g) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta right target g) := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let f := periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
    H N beta left right target
  let w := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta left right target g)
  let v := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
    H N hN beta hbeta right target
  let nu := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
    H N beta left right target
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hw : AEMeasurable w mu := by
    exact
      ((periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_continuous
          H N beta left right target).measurable.ennreal_ofReal).aemeasurable
  have hv : AEMeasurable v mu := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
        H N hN beta hbeta right target).measurable.aemeasurable
  have hRawInt : Integrable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta left right target g) mu :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_integrable
      H N beta left right target
  have hfExp : Integrable (fun g => Real.exp (f g)) mu := by
    have hEq : (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => Real.exp (f g)) =
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta left right target g) := by
      funext g
      exact periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight_exp
        H N beta left right target g
    rw [hEq]
    exact hRawInt
  have hNu : nu = doobWeightedMeasure mu w := by
    calc
      nu = mu.tilted f := rfl
      _ = doobWeightedMeasure mu
          (fun g => ENNReal.ofReal (Real.exp (f g))) :=
        (p4Q2AW_doobExp_eq_tilted mu f hfExp).symm
      _ = doobWeightedMeasure mu w := by
        congr 1
        funext g
        exact congrArg ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight_exp
            H N beta left right target g)
  let Z := periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
    H N beta left right target
  have hMass : doobWeightMass mu w = ENNReal.ofReal Z := by
    change
      (∫⁻ g, ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta left right target g) ∂mu) =
      ENNReal.ofReal
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta left right target g ∂mu)
    exact (ofReal_integral_eq_lintegral_ofReal hRawInt
      (ae_of_all mu fun g =>
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
          H N beta left right target g).le)).symm
  have hZpos : 0 < Z :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_pos
      H N hN beta hbeta left right target
  have hm0 : doobWeightMass mu w ≠ 0 := by
    rw [hMass]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hZpos)
  have hmtop : doobWeightMass mu w ≠ ∞ := by
    rw [hMass]
    exact ENNReal.ofReal_ne_top
  change doobWeightedMeasure nu v =
    doobWeightedMeasure mu (fun g => w g * v g)
  rw [hNu]
  exact p4Q2AW_doobWeightedMeasure_assoc mu w v hw hv hm0 hmtop

/-- The literal continuous-physical-vacuum Wilson JOINT density
restricted to one actual right-link fiber, normalized ONCE against
the unmodified SU(N) Haar probability. This is the intermediate
direct-target observable needed for the AV coordinate identification. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (fun g => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
        H N hN beta hbeta left right target g))

/-- Actual ORIGINAL one-slab continuous physical joint density, normalized
on one right link, equals the precise AS/AT Wilson-then-physical-vacuum
two-step posterior PROBABILITY, for EVERY continuous-vacuum context.
The anchor constant cancels using genuine positive finite Wilson data. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber_eq_ATPosterior
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber
      H N hN beta hbeta left right target =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
      H N hN beta hbeta left right target := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let w := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta left right target g)
  let v := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
    H N hN beta hbeta right target
  let C : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
      (Omega left * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left right)
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos
      (inv_pos.mpr
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
          H N hN beta hbeta))
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta left)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H N beta left right))
  have hPair (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
          H N hN beta hbeta left right target g) =
      (w g * v g) * ENNReal.ofReal C := by
    let W := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta left right target g
    let V := Omega (Function.update right target g)
    have hWpos : 0 ≤ W :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta left right target g).le
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
            H N hN beta hbeta left right target g) =
          ENNReal.ofReal (C * (W * V)) := by
            rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight_eq]
      _ = ENNReal.ofReal C * (ENNReal.ofReal W * ENNReal.ofReal V) := by
        rw [ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_mul hWpos]
      _ = (w g * v g) * ENNReal.ofReal C := by
        change ENNReal.ofReal C * (ENNReal.ofReal W * ENNReal.ofReal V) =
          (ENNReal.ofReal W * ENNReal.ofReal V) * ENNReal.ofReal C
        ac_rfl
  have hw : AEMeasurable w mu :=
    ((periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_continuous
        H N beta left right target).measurable.ennreal_ofReal).aemeasurable
  have hv : AEMeasurable v mu :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
      H N hN beta hbeta right target).measurable.aemeasurable
  have hcv : ENNReal.ofReal C ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hCpos)
  have hctop : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber
        H N hN beta hbeta left right target =
      doobWeightedMeasure mu (fun g => (w g * v g) * ENNReal.ofReal C) := by
        unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber
        apply congrArg (doobWeightedMeasure mu)
        funext g
        exact hPair g
    _ = doobWeightedMeasure mu (fun g => w g * v g) :=
      p4Q2AW_doobWeightedMeasure_mul_const mu (fun g => w g * v g)
        (ENNReal.ofReal C) (hw.mul hv) hcv hctop
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
          H N hN beta hbeta left right target :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabATPosteriorLaw_eq_HaarDoob_localWilson_mul_continuousVacuum
        H N hN beta hbeta left right target).symm

end
end MathlibAnalytic
end MGAP4D
