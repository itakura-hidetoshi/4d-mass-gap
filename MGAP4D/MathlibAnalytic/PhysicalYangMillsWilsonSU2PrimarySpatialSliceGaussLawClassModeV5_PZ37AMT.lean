import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimarySpatialSliceHaarPhysicalGaugeModeV5_PZ37AMS
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyContinuousGramSchmidtClassFunction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawProjection
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMT — native Gauss-law descent of the AMS primary spatial modes

All statements are on the original time-zero spatial-slice SU(2) Haar space.
This leaf relates the four-edge cyclic holonomy used by the AMS Haar isometry
to the original oriented spatial plaquette, then uses the existing continuous
Gram–Schmidt class-function representative to prove actual gauge-pullback
invariance in L², without an assumed OS/physical one-slab identification.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMT_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMT_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMT_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMT_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMT_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMT_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AMT_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AMT_haarLeftInvariant :
    Measure.IsMulLeftInvariant
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The canonical native time-zero oriented spatial plaquette has exactly the
original four positive link values, in the same order as the AMS Fin 4
restriction. This is geometry, not a gauge-fixing identification. -/
theorem p4Q2PZ37AMT_spatialHolonomy_eq_orientedFourEdge
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) =
      orientedFourEdgePlaquetteWord
        (fun k => A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H k)) := by
  rfl

/-- The actual oriented time-zero spatial plaquette holonomy is a conjugate
of the cyclic four-Haar word used by the AMS L² isometry. -/
theorem p4Q2PZ37AMT_spatialHolonomy_eq_conj_cyclic
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) =
      (A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H 0) *
        A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H 1)) *
      p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A *
      (A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H 0) *
        A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H 1))⁻¹ := by
  rw [p4Q2PZ37AMT_spatialHolonomy_eq_orientedFourEdge]
  simpa only [p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy] using
    (orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord
      (fun k => A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H k)))

/-- The continuous Gram–Schmidt class function cannot distinguish the actual
oriented primary spatial plaquette from its cyclic four-Haar representative. -/
theorem p4Q2PZ37AMT_continuousMode_cyclic_eq_intrinsic
    (H k : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)) := by
  rw [p4Q2PZ37AMT_spatialHolonomy_eq_conj_cyclic]
  exact (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_conjInvariant
    k
    (A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H 0) *
      A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H 1))
    (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)).symm

/-- Invariance at every actual native spatial gauge transform, pointwise
on the same time-zero SU(2) configuration carrier. -/
theorem p4Q2PZ37AMT_continuousMode_cyclic_gaugeInvariant
    (H k : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A)) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) := by
  calc
    _ = specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A)
            (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)) :=
        p4Q2PZ37AMT_continuousMode_cyclic_eq_intrinsic H k _
    _ = specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
            (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)) := by
        rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
        exact specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_conjInvariant
          k
          (γ (p4Q2PZ37AMS_primarySpatialSlicePlaquette H).1)
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
            (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
    _ = _ := (p4Q2PZ37AMT_continuousMode_cyclic_eq_intrinsic H k A).symm

/-- The AMS Haar-L² Gram–Schmidt vector has the actual continuous pointwise
representative on the native time-zero spatial slice, almost everywhere. -/
theorem p4Q2PZ37AMT_spatialMode_coeFn
    (H k : ℕ) :
    (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2)
        (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k)
      =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
      (fun A => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
  rw [← specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp k]
  let hMP := p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2
  let f : SpecialUnitaryNormalizedHaarL2 2 :=
    ContinuousMap.toLp (E := ℝ) 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k)
  have hComp :
      p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2 f
          =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
        f ∘ p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 := by
    exact Lp.coeFn_compMeasurePreserving f hMP
  have hSource :
      f =ᵐ[normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
        specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k)
  have hPulled :
      f ∘ p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
          =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
        (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k) ∘
          p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 :=
    hMP.quasiMeasurePreserving.ae_eq hSource
  exact hComp.trans (by simpa [Function.comp_def] using hPulled)

/-- Every theorem-generated AMS L² orthonormal mode belongs to the *actual*
closed Gauss-law fixed Hilbert submodule; no abstract fixed-vector assumption. -/
theorem p4Q2PZ37AMT_spatialMode_mem_closedGaussLaw
    (H k : ℕ) :
    (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2)
        (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k) ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
        H 2 := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_mem]
  intro γ
  let f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) :=
    (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2)
      (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k)
  change periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
    H 2 γ f = f
  let g := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  have hMP :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hObs :
      f =ᵐ[μ]
        (fun A => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) :=
    p4Q2PZ37AMT_spatialMode_coeFn H k
  have hGauge :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H 2 γ f =ᵐ[μ] f ∘ g := by
    exact Lp.coeFn_compMeasurePreserving f hMP
  have hObsPull :
      f ∘ g =ᵐ[μ]
        (fun A => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 (g A))) := by
    simpa [g, Function.comp_def] using
      (hMP.quasiMeasurePreserving.ae_eq hObs)
  have hGaugeObs := hGauge.trans hObsPull
  apply Lp.ext
  filter_upwards [hGaugeObs, hObs] with A hleft hright
  calc
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H 2 γ f) A =
        specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 (g A)) := hleft
    _ = specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
          (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) := by
        exact p4Q2PZ37AMT_continuousMode_cyclic_gaugeInvariant H k γ A
    _ = f A := hright.symm

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMT_spatialHolonomy_eq_orientedFourEdge
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMT_spatialHolonomy_eq_conj_cyclic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMT_continuousMode_cyclic_eq_intrinsic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMT_continuousMode_cyclic_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMT_spatialMode_coeFn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMT_spatialMode_mem_closedGaussLaw
