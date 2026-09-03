import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentUnfixedPathKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryMomentAutomaticL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMomentAutomaticL2SpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMomentAutomaticL2SpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMomentAutomaticL2SpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMomentAutomaticL2SpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- For a bounded continuous positive-half observable, the scalar boundary Gram
feature is jointly measurable in the open-half and shared-boundary variables.

The proof uses the already-established square-root representation by the
orientation-corrected finite Wilson Gibbs density. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_joint_measurable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f p.2 p.1) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hdiag : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        (p.2, (p.1, periodicHypercubicEvenOpenHalfOrientationCorrection H p.1))) :=
    measurable_snd.prodMk
      (measurable_fst.prodMk (hc.comp measurable_fst))
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hsqrt : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (p.2,
              (p.1, periodicHypercubicEvenOpenHalfOrientationCorrection H p.1))).toReal)) :=
    Real.continuous_sqrt.measurable.comp
      ((ENNReal.measurable_toReal.comp hd).comp hdiag)
  have hcompleted : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.2 p.1) := by
    have heq :
        (fun p : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta p.2 p.1) =
          fun p =>
            Real.sqrt
              ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
                H N hN beta hbeta
                (p.2,
                  (p.1, periodicHypercubicEvenOpenHalfOrientationCorrection H p.1))).toReal) := by
      funext p
      exact
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity
          H N hN beta hbeta p.2 p.1
    rw [heq]
    exact hsqrt
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  exact hcompleted.mul (f.continuous.measurable.comp measurable_fst)

/-- The joint boundary/open-half Gram feature is integrable under the product
of the two finite normalized Haar laws. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_joint_integrable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f p.2 p.1)
      ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
        (periodicHypercubicEvenBoundaryHaarMeasure H N)) := by
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let nu := periodicHypercubicEvenBoundaryHaarMeasure H N
  let bound :=
    Real.sqrt
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
      ‖f‖
  letI : IsFiniteMeasure mu := by
    dsimp [mu, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  letI : IsFiniteMeasure nu := by
    dsimp [nu, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  have hm :=
    periodicHypercubicEvenBoundaryObservableGramFeature_joint_measurable_of_boundedContinuous
      H N hN beta hbeta f
  apply Integrable.of_bound hm.aestronglyMeasurable bound
  filter_upwards with p
  exact
    periodicHypercubicEvenBoundaryObservableGramFeature_norm_le_of_boundedContinuous
      H N hN beta hbeta f p.2 p.1

/-- The shared-boundary moment of a bounded continuous positive-half observable
is integrable as a function of the shared boundary.  This is a direct Fubini
consequence of joint finite-Haar integrability. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_integrable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta f)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  have hjoint :=
    periodicHypercubicEvenBoundaryObservableGramFeature_joint_integrable_of_boundedContinuous
      H N hN beta hbeta f
  simpa [periodicHypercubicEvenBoundaryObservableMoment] using
    hjoint.integral_prod_right

/-- A uniform finite-Haar bound for the shared-boundary moment.  The open-half
Haar mass is kept explicit, so this statement does not depend on a fragile
probability-measure instance being synthesized for the named product measure. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_norm_le_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta f b‖ ≤
      (Real.sqrt
          (((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
        ‖f‖) *
        (periodicHypercubicEvenOpenHalfHaarMeasure H N).real univ := by
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  letI : IsFiniteMeasure mu := by
    dsimp [mu, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  unfold periodicHypercubicEvenBoundaryObservableMoment
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  exact
    periodicHypercubicEvenBoundaryObservableGramFeature_norm_le_of_boundedContinuous
      H N hN beta hbeta f b x

/-- Every bounded continuous positive-half Wilson observable has a genuine
shared-boundary `L²` Gram moment.  Thus `MemLp` is theorem-generated rather than
an extra certificate hypothesis. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_memLp_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    MemLp
      (periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta f)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  let nu := periodicHypercubicEvenBoundaryHaarMeasure H N
  let bound :=
    (Real.sqrt
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
      ‖f‖) *
      (periodicHypercubicEvenOpenHalfHaarMeasure H N).real univ
  letI : IsFiniteMeasure nu := by
    dsimp [nu, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  have hint :=
    periodicHypercubicEvenBoundaryObservableMoment_integrable_of_boundedContinuous
      H N hN beta hbeta f
  apply MemLp.of_bound hint.aestronglyMeasurable bound
  filter_upwards with b
  exact
    periodicHypercubicEvenBoundaryObservableMoment_norm_le_of_boundedContinuous
      H N hN beta hbeta f b

section ActualWilsonCarrier

variable
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- The actual `n`-th finite Wilson OS carrier has automatic shared-boundary
`L²` membership.  No `boundaryMoment_memLp` assumption is needed. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
  exact
    periodicHypercubicEvenBoundaryObservableMoment_memLp_of_boundedContinuous
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)

end ActualWilsonCarrier

end MathlibAnalytic
end MGAP4D

end
