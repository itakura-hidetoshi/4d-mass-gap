import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryMomentCanonicalL2SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMomentCanonicalL2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMomentCanonicalL2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMomentCanonicalL2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMomentCanonicalL2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMomentCanonicalL2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The completed positive Wilson Gram feature is jointly measurable in the
shared-boundary and open-half variables.  The earlier reflection-positivity
route only needed measurability after fixing the boundary; the joint statement
is the missing input for treating the boundary moment itself as an `L²`
function. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_joint_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have harg : Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (z.1,
          (z.2,
            periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))) := by
    exact measurable_fst.prodMk
      (measurable_snd.prodMk (hc.comp measurable_snd))
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hsqrt : Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (z.1,
              (z.2,
                periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))).toReal)) :=
    Real.continuous_sqrt.measurable.comp
      ((ENNReal.measurable_toReal.comp hd).comp harg)
  have heq :
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) =
        fun z =>
          Real.sqrt
            ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
              H N hN beta hbeta
              (z.1,
                (z.2,
                  periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))).toReal) := by
    funext z
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity
        H N hN beta hbeta z.1 z.2
  rw [heq]
  exact hsqrt

/-- A bounded continuous positive-half observable gives a jointly measurable
observable-weighted boundary Gram feature. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_joint_measurable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Measurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta (fun x => f x) z.1 z.2) := by
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  exact
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_joint_measurable
      H N hN beta hbeta).mul
      (f.continuous.measurable.comp measurable_snd)

/-- The scalar boundary moment of a bounded continuous positive-half observable
is strongly measurable as a function of the shared boundary. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_stronglyMeasurable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    StronglyMeasurable
      (fun b =>
        periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta (fun x => f x) b) := by
  have hjoint : StronglyMeasurable
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta (fun x => f x) z.1 z.2) :=
    (periodicHypercubicEvenBoundaryObservableGramFeature_joint_measurable_of_boundedContinuous
      H N hN beta hbeta f).stronglyMeasurable
  have hint :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := periodicHypercubicEvenOpenHalfHaarMeasure H N) hjoint
  simpa [periodicHypercubicEvenBoundaryObservableMoment] using hint

/-- The boundary moment inherits an explicit finite pointwise bound from the
bounded-continuous observable and the finite open-half Haar measure. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_norm_le_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta (fun x => f x) b‖ ≤
      (Real.sqrt
          (((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
        ‖f‖) *
        (periodicHypercubicEvenOpenHalfHaarMeasure H N).real Set.univ := by
  letI : IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  unfold periodicHypercubicEvenBoundaryObservableMoment
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun x =>
      periodicHypercubicEvenBoundaryObservableGramFeature_norm_le_of_boundedContinuous
        H N hN beta hbeta f b x)

/-- No `L²` membership hypothesis is needed for actual bounded-continuous
Wilson boundary moments: joint measurability and the finite-measure pointwise
bound generate `MemLp 2` directly. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_memLp_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    MemLp
      (fun b =>
        periodicHypercubicEvenBoundaryObservableMoment
          H N hN beta hbeta (fun x => f x) b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  letI : IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
    dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  let C : ℝ :=
    (Real.sqrt
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
      ‖f‖) *
      (periodicHypercubicEvenOpenHalfHaarMeasure H N).real Set.univ
  exact MemLp.of_bound
    (periodicHypercubicEvenBoundaryObservableMoment_stronglyMeasurable_of_boundedContinuous
      H N hN beta hbeta f).aestronglyMeasurable
    C
    (Filter.Eventually.of_forall fun b =>
      periodicHypercubicEvenBoundaryObservableMoment_norm_le_of_boundedContinuous
        H N hN beta hbeta f b)

/-- The Gram-feature integrability stored in the older boundary-gap certificate
is theorem-generated for every actual approximating Wilson OS carrier. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryGramFeature_integrable
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) := by
  simpa using
    periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)
      b

/-- Likewise, `MemLp 2` of every actual physical boundary moment is generated
from the finite Wilson model rather than supplied as a certificate field. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp
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

/-- Canonical `L²` representative of the actual finite Wilson boundary moment.
Unlike the older constructor, this definition has no external `MemLp`
argument. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
    S D halfExtent N hN beta hbeta B hInvariant n F
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp
      S D halfExtent N hN beta hbeta B hInvariant n F)

/-- The canonical boundary `L²` representative has exactly the OS carrier
seminorm.  Thus the shared-boundary realization loses no finite OS norm
information; only linear compatibility of the chosen half-observable pullback
remains before it can be promoted to an isometric linear embedding of the
separated/completed OS Hilbert space. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 =
      ‖F‖ ^ 2 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let hF :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp
      S D halfExtent N hN beta hbeta B hInvariant n F
  change
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF‖ ^ 2 =
      ‖F‖ ^ 2
  rw [physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta B hInvariant n F hF]
  rw [← physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
    S D halfExtent N hN beta hbeta B hInvariant n F
    (fun b =>
      physicalYangMillsEvenPeriodicWilsonOSBoundaryGramFeature_integrable
        S D halfExtent N hN beta hbeta B hInvariant n F b)]
  rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
    S D halfExtent N hN beta hbeta B hInvariant n F]
  exact Pn.osQuadraticValue_eq_norm_sq F

/-- Norm-level form of the exact finite OS/boundary `L²` isometry. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_eq
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ = ‖F‖ := by
  have hsq :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n F
  nlinarith
    [norm_nonneg
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F),
     norm_nonneg F]

end MathlibAnalytic
end MGAP4D

end
