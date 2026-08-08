import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualAdjointSynthesisBoundaryTransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDenseStateMap
import MGAP4D.MathlibAnalytic.RealLinearDenseIsometricAmbientExtension

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance boundedPositiveHalfAnalysisSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundedPositiveHalfAnalysisSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundedPositiveHalfAnalysisSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundedPositiveHalfAnalysisSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundedPositiveHalfAnalysisSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundedPositiveHalfAnalysisSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The exact remaining bounded-lifting datum for the coherent finite-Wilson
positive-half analysis.

No quotient, completion, or intertwining compatibility is stored here.  The
only analytic input is a carrier-level operator bound with respect to the OS
seminorm. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) where
  bound : ℕ → NNReal → ℝ
  bound_nonneg : ∀ n t, 0 ≤ bound n t
  translatedPositiveHalfL2_norm_le :
    ∀ (n : ℕ) (t : NNReal)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      ‖Q.translatedPositiveHalfL2LinearMap hInvariant C n t F‖ ≤
        bound n t * ‖F‖

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}

/-- The carrier bound rewritten against the norm of the represented physical
state, exactly in the form required by Mathlib's `LinearMap.extendOfNorm`. -/
theorem norm_le_physicalState
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    ‖Q.translatedPositiveHalfL2LinearMap hInvariant C n t F‖ ≤
      R.bound n t *
        ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalStateLinearMap F‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change ‖Q.translatedPositiveHalfL2LinearMap hInvariant C n t F‖ ≤
    R.bound n t * ‖Pn.physicalStateLinearMap F‖
  rw [Pn.physicalStateLinearMap_apply, Pn.norm_physicalState]
  exact R.translatedPositiveHalfL2_norm_le n t F

/-- The time-dependent positive-half analysis extends canonically from the OS
carrier through the null quotient and Hilbert completion.  No separate
null-space compatibility field is needed: it follows from the norm bound. -/
noncomputable def physicalHilbertAnalysis
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert →L[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  (Q.translatedPositiveHalfL2LinearMap hInvariant C n t).extendOfNorm
    Pn.physicalStateLinearMap

/-- The Hilbert-completed analysis agrees exactly with the carrier analysis on
every represented physical state. -/
@[simp] theorem physicalHilbertAnalysis_apply_physicalState
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    R.physicalHilbertAnalysis n t
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F) =
      Q.translatedPositiveHalfL2LinearMap hInvariant C n t F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    (Q.translatedPositiveHalfL2LinearMap hInvariant C n t).extendOfNorm
        Pn.physicalStateLinearMap (Pn.physicalState F) =
      Q.translatedPositiveHalfL2LinearMap hInvariant C n t F
  rw [← Pn.physicalStateLinearMap_apply]
  exact LinearMap.extendOfNorm_eq
    Pn.physicalStateLinearMap_denseRange
    ⟨R.bound n t, R.norm_le_physicalState n t⟩ F

/-- Completion preserves the carrier norm bound. -/
theorem physicalHilbertAnalysis_opNorm_le
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖R.physicalHilbertAnalysis n t‖ ≤ R.bound n t := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    ‖(Q.translatedPositiveHalfL2LinearMap hInvariant C n t).extendOfNorm
        Pn.physicalStateLinearMap‖ ≤ R.bound n t
  exact LinearMap.opNorm_extendOfNorm_le
    Pn.physicalStateLinearMap_denseRange
    (R.bound_nonneg n t)
    (R.norm_le_physicalState n t)

/-- Canonical global boundary analysis.  First project a boundary vector to the
closed physical OS boundary range, invert `Ĵ_n` there, then apply the completed
positive-half analysis. -/
noncomputable def completedBoundaryAnalysis
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  realLinearDenseIsometricAmbientExtension
    (Q.translatedPositiveHalfL2LinearMap hInvariant C n t)
    Pn.physicalStateLinearMap
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    Pn.physicalStateLinearMap_denseRange
    (R.bound n t)
    (R.bound_nonneg n t)
    (R.norm_le_physicalState n t)

/-- The global boundary analysis is the exact original `U_{n,t}` on every
canonical Wilson boundary moment. -/
@[simp] theorem completedBoundaryAnalysis_apply_canonicalBoundaryMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    R.completedBoundaryAnalysis n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      Q.translatedPositiveHalfL2LinearMap hInvariant C n t F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [← Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
  exact realLinearDenseIsometricAmbientExtension_apply
    (Q.translatedPositiveHalfL2LinearMap hInvariant C n t)
    Pn.physicalStateLinearMap
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    Pn.physicalStateLinearMap_denseRange
    (R.bound n t)
    (R.bound_nonneg n t)
    (R.norm_le_physicalState n t)
    F

/-- Orthogonal projection and Hilbert completion introduce no loss in the
analysis operator norm. -/
theorem completedBoundaryAnalysis_opNorm_le
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖R.completedBoundaryAnalysis n t‖ ≤ R.bound n t := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact realLinearDenseIsometricAmbientExtension_opNorm_le
    (Q.translatedPositiveHalfL2LinearMap hInvariant C n t)
    Pn.physicalStateLinearMap
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)
    Pn.physicalStateLinearMap_denseRange
    (R.bound n t)
    (R.bound_nonneg n t)
    (R.norm_le_physicalState n t)

/-- The actual Wilson adjoint synthesis of the generated global analysis is
exactly the completed OS boundary transfer on every canonical moment. -/
theorem actualSynthesis_completedBoundaryAnalysis_apply_canonicalBoundaryMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n).comp (R.completedBoundaryAnalysis n t)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      Q.completedBoundaryTransfer hInvariant C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) := by
  rw [ContinuousLinearMap.comp_apply,
    R.completedBoundaryAnalysis_apply_canonicalBoundaryMoment]
  exact (Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment_eq_actualSynthesis
    hInvariant C n t F).symm

/-- In particular, the vacuum-centered intertwining field required by the
actual-adjoint gap certificate is generated automatically from the one carrier
norm bound. -/
theorem actualSynthesis_completedBoundaryAnalysis_vacuumCentered_intertwining
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n).comp (R.completedBoundaryAnalysis n t)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2)
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)) := by
  rw [R.actualSynthesis_completedBoundaryAnalysis_apply_canonicalBoundaryMoment]
  exact Q.completedBoundaryTransfer_vacuumCentered_intertwining hInvariant C n t F

end PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData

/-- Reduced actual-adjoint gap data after quotient/completion/intertwining have
been generated.  The model-specific analytic remainder is now exactly:

1. a carrier norm bound for `U_{n,t}`;
2. the scalar norm-product inequality using that bound.

All Hilbert-space extension and actual synthesis intertwining are derived. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) where
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  analysisBound : ℕ → NNReal → ℝ
  analysisBound_nonneg : ∀ n t, 0 ≤ analysisBound n t
  translatedPositiveHalfL2_norm_le :
    ∀ (n : ℕ) (t : NNReal)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      ‖Q.translatedPositiveHalfL2LinearMap hInvariant C n t F‖ ≤
        analysisBound n t * ‖F‖
  factor_bound :
    ∀ (n : ℕ) (t : NNReal),
      ‖physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n‖ * analysisBound n t ≤
        Real.sqrt (quadraticDecayFactor t)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}

/-- Forget only the scalar gap data, retaining the exact bounded-analysis
information used to generate the Hilbert/global lift. -/
noncomputable def toBoundedPositiveHalfAnalysisData
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisGapCertificate
      S D halfExtent N hN beta hbeta Q hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisData
      S D halfExtent N hN beta hbeta Q hInvariant C where
  bound := R.analysisBound
  bound_nonneg := R.analysisBound_nonneg
  translatedPositiveHalfL2_norm_le := R.translatedPositiveHalfL2_norm_le

/-- The reduced carrier-bound package generates the full #1469 actual-adjoint
factorized transfer certificate.  In particular the global analysis map and
its exact intertwining are no longer independent physical inputs. -/
noncomputable def toActualAdjointSynthesisBoundaryTransferGapCertificate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisGapCertificate
      S D halfExtent N hN beta hbeta Q hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C where
  mass := R.mass
  mass_pos := R.mass_pos
  quadraticDecayFactor := R.quadraticDecayFactor
  quadraticDecayFactor_nonneg := R.quadraticDecayFactor_nonneg
  slope_tendsto := R.slope_tendsto
  exchange := R.exchange
  analysis := fun n t =>
    R.toBoundedPositiveHalfAnalysisData.completedBoundaryAnalysis n t
  boundaryMoment_intertwining := by
    intro n t
    dsimp only
    intro F
    exact
      R.toBoundedPositiveHalfAnalysisData.actualSynthesis_completedBoundaryAnalysis_vacuumCentered_intertwining
        n t F
  factor_opNorm_mul_le := by
    intro n t
    calc
      ‖physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n‖ *
          ‖R.toBoundedPositiveHalfAnalysisData.completedBoundaryAnalysis n t‖ ≤
        ‖physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n‖ * R.analysisBound n t := by
            exact mul_le_mul_of_nonneg_left
              (R.toBoundedPositiveHalfAnalysisData.completedBoundaryAnalysis_opNorm_le n t)
              (norm_nonneg _)
      _ ≤ Real.sqrt (R.quadraticDecayFactor t) := R.factor_bound n t

end PhysicalYangMillsEvenPeriodicWilsonOSBoundedPositiveHalfAnalysisGapCertificate

end MathlibAnalytic
end MGAP4D

end
