import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHilbertGram
import Mathlib.MeasureTheory.Function.L2Space

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe u v

/-- An iterated real Hilbert Gram integral is the squared norm of its Bochner
moment.  This is the analytic identity underlying the compact-group
Peter--Weyl reflection-positivity argument. -/
theorem iterated_integral_real_inner_eq_norm_integral_sq
    {X : Type u} {H : Type v}
    [MeasurableSpace X]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (mu : Measure X)
    (g : X → H)
    (hg : Integrable g mu) :
    (∫ x, ∫ y, inner ℝ (g x) (g y) ∂mu ∂mu) =
      ‖∫ x, g x ∂mu‖ ^ 2 := by
  let M : H := ∫ x, g x ∂mu
  calc
    (∫ x, ∫ y, inner ℝ (g x) (g y) ∂mu ∂mu) =
        ∫ x, inner ℝ (g x) M ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact integral_inner hg (g x)
    _ = ∫ x, inner ℝ M (g x) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (real_inner_comm (g x) M).symm
    _ = inner ℝ M M := integral_inner hg M
    _ = ‖M‖ ^ 2 := inner_self_eq_norm_sq_to_K M
    _ = ‖∫ x, g x ∂mu‖ ^ 2 := rfl

/-- Half-lattice Bochner Gram data for the actual compact Wilson pullback form.

`amplitude` is the pulled-back positive-time observable factor, while `feature`
contains the crossing-plane matrix coefficients.  Their product is integrated
in a real Hilbert feature space.  The feature space may be infinite-dimensional,
so this structure accommodates countable Peter--Weyl expansions. -/
structure PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  HalfConfiguration : Type
  [halfMeasurableSpace : MeasurableSpace HalfConfiguration]
  halfMeasure : Measure HalfConfiguration
  FeatureHilbert : Type
  [featureNormedAddCommGroup : NormedAddCommGroup FeatureHilbert]
  [featureInnerProductSpace : InnerProductSpace ℝ FeatureHilbert]
  [featureCompleteSpace : CompleteSpace FeatureHilbert]
  amplitude : ℕ → D.positiveTimeSubalgebra → HalfConfiguration → ℝ
  feature : ℕ → HalfConfiguration → FeatureHilbert
  weightedFeature :
    ℕ → D.positiveTimeSubalgebra → HalfConfiguration → FeatureHilbert :=
      fun n F x => amplitude n F x • feature n x
  weightedFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable (weightedFeature n F) halfMeasure
  pullbackForm_eq_iterated_inner :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      D.orientedWilsonPullbackForm G L n F =
        ∫ x, ∫ y,
          inner ℝ (weightedFeature n F x) (weightedFeature n F y)
          ∂halfMeasure ∂halfMeasure

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate.halfMeasurableSpace
  PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate.featureNormedAddCommGroup
  PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate.featureInnerProductSpace
  PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate.featureCompleteSpace

/-- The Bochner feature moment associated with a positive-time observable. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate.moment
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) : C.FeatureHilbert :=
  ∫ x, C.weightedFeature n F x ∂C.halfMeasure

/-- The half-lattice Bochner kernel decomposition generates the Hilbert Gram
identity; the squared-norm representation is not an independent assumption. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate.toHilbertGramCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate G L D) :
    PhysicalYangMillsOrientedWilsonOSHilbertGramCertificate G L D where
  FeatureHilbert := C.FeatureHilbert
  moment := C.moment
  pullbackForm_eq_norm_sq n F := by
    rw [C.pullbackForm_eq_iterated_inner]
    exact iterated_integral_real_inner_eq_norm_integral_sq
      C.halfMeasure (C.weightedFeature n F)
      (C.weightedFeature_integrable n F)

/-- A Bochner/Peter--Weyl Gram certificate makes every physical approximating
state reflection positive. -/
theorem physical_yang_mills_oriented_bochnerGram_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate G L D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_hilbertGram_approximating_reflectionPositive
    G L D C.toHilbertGramCertificate n

/-- A half-lattice Bochner/Peter--Weyl Gram decomposition of the actual compact
Wilson laws yields continuum Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_bochnerGram_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate G L D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_hilbertGram_continuum_reflectionPositive
    G L D C.toHilbertGramCertificate

end

end MathlibAnalytic
end MGAP4D
