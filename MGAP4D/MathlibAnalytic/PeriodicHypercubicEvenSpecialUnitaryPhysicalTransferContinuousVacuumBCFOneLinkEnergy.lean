import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumCenteredOneLinkGap
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalVarianceBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance continuousVacuumBCFOneLinkEnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The canonical centered one-link fiber observable attached to a bounded
continuous Wilson observable.  It is centered by the literal full Wilson
one-link heat-bath expectation, not by an externally chosen representative. -/
def periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  O (C.base.replaceLink A fullTarget g) -
    C.singleLinkHeatBathProjection fullTarget O A

/-- The canonical centered BCF fiber is square-integrable under the literal
full Wilson one-link conditional probability law.  Compactness and the
heat-bath norm contraction give the uniform bound `2 * ‖O‖`; no extra local
integrability hypothesis is introduced. -/
theorem periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_memLp
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
        H N hN beta hbeta O A target)
      2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let X : C.base.Gauge → ℝ := fun g =>
    O (C.base.replaceLink A fullTarget g) -
      C.singleLinkHeatBathProjection fullTarget O A
  have hStrong : StronglyMeasurable X := by
    apply StronglyMeasurable.sub
    · exact
        (O.continuous.comp
          (continuous_compact_oriented_replaceLink C A fullTarget)).stronglyMeasurable
    · exact stronglyMeasurable_const
  have hBound : ∀ g, ‖X g‖ ≤ 2 * ‖O‖ := by
    intro g
    rw [Real.norm_eq_abs]
    have hO : |O (C.base.replaceLink A fullTarget g)| ≤ ‖O‖ :=
      O.norm_coe_le_norm _
    have hP : |C.singleLinkHeatBathProjection fullTarget O A| ≤ ‖O‖ :=
      continuous_compact_oriented_singleLinkHeatBathProjection_abs_le_norm
        C fullTarget O A
    calc
      |X g| ≤ |O (C.base.replaceLink A fullTarget g)| +
          |C.singleLinkHeatBathProjection fullTarget O A| := abs_sub _ _
      _ ≤ ‖O‖ + ‖O‖ := add_le_add hO hP
      _ = 2 * ‖O‖ := by ring
  have hLp : MemLp X 2 (C.singleLinkConditionalMeasure A fullTarget) :=
    MemLp.of_bound hStrong.aestronglyMeasurable (2 * ‖O‖)
      (Filter.Eventually.of_forall hBound)
  change MemLp X 2 (C.singleLinkConditionalMeasure A fullTarget)
  exact hLp

/-- The canonical BCF fiber is exactly centered under the literal Wilson
one-link conditional law. -/
theorem periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_integral_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∫ g,
      periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
        H N hN beta hbeta O A target g ∂
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) = 0 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let μ := C.singleLinkConditionalMeasure A fullTarget
  let X : C.base.Gauge → ℝ := fun g =>
    O (C.base.replaceLink A fullTarget g) -
      C.singleLinkHeatBathProjection fullTarget O A
  have hprob : IsProbabilityMeasure μ :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A fullTarget
  letI : IsProbabilityMeasure μ := hprob
  have hXLp : MemLp X 2 μ := by
    change MemLp
      (periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
        H N hN beta hbeta O A target) 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
    exact
      periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_memLp
        H N hN beta hbeta O A target
  have hXInt : Integrable X μ := hXLp.integrable (by norm_num)
  have hConst : Integrable
      (fun _g : C.base.Gauge => C.singleLinkHeatBathProjection fullTarget O A) μ :=
    integrable_const _
  have hObs : Integrable (fun g : C.base.Gauge =>
      O (C.base.replaceLink A fullTarget g)) μ := by
    have hEq : (fun g : C.base.Gauge => O (C.base.replaceLink A fullTarget g)) =
        fun g => X g + C.singleLinkHeatBathProjection fullTarget O A := by
      funext g
      simp [X]
    rw [hEq]
    exact hXInt.add hConst
  change ∫ g : C.base.Gauge,
    (O (C.base.replaceLink A fullTarget g) -
      C.singleLinkHeatBathProjection fullTarget O A) ∂μ = 0
  rw [integral_sub hObs hConst]
  change C.singleLinkHeatBathProjection fullTarget O A -
      ∫ _g : C.base.Gauge, C.singleLinkHeatBathProjection fullTarget O A ∂μ = 0
  simp

/-- For the canonical centered fiber, the extended squared residual in #3691
is exactly `ofReal` of the native Wilson conditional variance used by the
existing global Gibbs `L²` heat-bath energy theory. -/
theorem periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_zeroResidual_eq_ofReal_conditionalVariance
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    doobCenteredSquaredResidual
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
      (periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
        H N hN beta hbeta O A target) 0 =
    ENNReal.ofReal
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalVarianceBCF
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) O A) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let μ := C.singleLinkConditionalMeasure A fullTarget
  let X := periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
    H N hN beta hbeta O A target
  have hX : MemLp X 2 μ := by
    change MemLp
      (periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
        H N hN beta hbeta O A target) 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
    exact
      periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_memLp
        H N hN beta hbeta O A target
  have hSq : Integrable (fun g => (X g) ^ 2) μ := by
    simpa only [Pi.pow_apply] using hX.integrable_sq
  change (∫⁻ g, ENNReal.ofReal ((X g - 0) ^ 2) ∂μ) =
    ENNReal.ofReal (C.singleLinkConditionalVarianceBCF fullTarget O A)
  simp only [sub_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal hSq
    (ae_of_all μ fun g => sq_nonneg (X g))]
  congr 1
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalVarianceBCF
  apply integral_congr_ae
  filter_upwards [] with g
  simp [X, C, fullTarget,
    periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF]

/-- Canonical observable form of the volume-uniform continuous-vacuum one-link
coercivity.  The left side is now the native Wilson conditional variance used
by the global Gibbs `L²` heat-bath theory, while the right side is the literal
continuous-physical-vacuum Doob variance. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_BCF_conditionalVariance_exp_neg_sixteen_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ENNReal.ofReal (Real.exp (-16 * beta)) *
      ENNReal.ofReal
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalVarianceBCF
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) O A) ≤
    evariance
      (periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
        H N hN beta hbeta O A target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
        H N hN beta hbeta A target) := by
  let X := periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF
    H N hN beta hbeta O A target
  have hX :=
    periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_memLp
      H N hN beta hbeta O A target
  have hmean :=
    periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_integral_eq_zero
      H N hN beta hbeta O A target
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_centered_zeroResidual_exp_neg_sixteen_lower_bound
      H N hN beta hbeta A target X hX hmean
  rw [periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLinkCenteredFiberBCF_zeroResidual_eq_ofReal_conditionalVariance
    H N hN beta hbeta O A target] at h
  exact h

/-- On the same canonical bounded-continuous core, the Gibbs average of the raw
full-Wilson conditional variance is exactly the squared global Gibbs `L²`
one-link projection defect.  Together with the preceding theorem this pins the
local `exp (-16 * beta)` comparison to the existing global heat-bath energy
carrier without any quotient-representative point evaluation. -/
theorem periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLink_integral_conditionalVarianceBCF_eq_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∫ A,
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalVarianceBCF
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) O A ∂
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
    ‖(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkHeatBathFluctuationL2
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  exact continuous_compact_oriented_integral_singleLinkConditionalVarianceBCF_eq_norm_sq
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) O

end

end MathlibAnalytic
end MGAP4D
