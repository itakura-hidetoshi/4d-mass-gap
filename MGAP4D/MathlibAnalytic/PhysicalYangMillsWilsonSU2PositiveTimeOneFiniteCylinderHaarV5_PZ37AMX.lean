import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2TwoModeFiniteCylinderTopOrthogonalV5_PZ37AMW
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMX — original positive-time one-slice Wilson-cylinder Haar lift

The independently push-certified AMW two-mode vector is already an actual
nonzero gauge-invariant physical SU(2) finite Wilson state and an a.e. concrete
time-zero spatial-plaquette Wilson cylinder. This next unit embeds that SAME
finite spatial-cylinder observable at strict positive time 1 of the ORIGINAL
positive-half-cylinder spatial path, under its original product spatial Haar
law, and proves it does not vanish.

The path Haar law is not the interacting Gibbs measure. This does NOT
provide a positive-time observable in arbitrary abstract OS D or identify
the completed OS boundary transfer with the original physical one-slab.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMX_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

-- Exact typeclass context of the existing pinned original SU(2) Haar modules.
-- Imports of other files' local instances do not export those instances.
local instance p4Q2PZ37AMX_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMX_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMX_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMX_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMX_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- Strict positive time 1 is inside the genuine original half-cylinder path
of H+2 spatial slices, including H=0. -/
def p4Q2PZ37AMX_positiveTimeOne
    (H : ℕ) :
    Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) :=
  ⟨1, by
    change 1 < (H + 1) + 1
    omega⟩

/-- Evaluation at the first positive-time spatial slice preserves the actual
independent spatial-slice normalized Haar marginal exactly. -/
theorem p4Q2PZ37AMX_positiveTimeOne_measurePreserving
    (H : ℕ) :
    MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 =>
        path (p4Q2PZ37AMX_positiveTimeOne H))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  simpa [μ, periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure]
    using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) => μ)
        (p4Q2PZ37AMX_positiveTimeOne H))

/-- Exact real Haar-L² linear isometry of an actual spatial-slice observable
to that SAME native finite Wilson cylinder at strict positive time one. -/
noncomputable def p4Q2PZ37AMX_positiveTimeOneL2Pullback
    (H : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) →ₗᵢ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 =>
      path (p4Q2PZ37AMX_positiveTimeOne H))
    (p4Q2PZ37AMX_positiveTimeOne_measurePreserving H)

/-- The original AMW finite two-Wilson-mode Gauss-law/top-orthogonal witness
has a NONZERO Haar-L² realization as a literal first-positive-time original
half-cylinder observable. The last equality is its actual time-one a.e.
pointwise cylinder representative. This is not yet a Gibbs/OS carrier state. -/
theorem p4Q2PZ37AMX_exists_nonzero_oneStepPositiveHalfWilsonCylinder
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      p4Q2PZ37AMX_positiveTimeOneL2Pullback H
        ((c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
          c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) ≠ 0 ∧
      p4Q2PZ37AMX_positiveTimeOneL2Pullback H
        ((c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
          c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
        =ᵐ[periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2]
          (fun path =>
            c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
              (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
                (path (p4Q2PZ37AMX_positiveTimeOne H))) +
            c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
              (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
                (path (p4Q2PZ37AMX_positiveTimeOne H)))) := by
  obtain ⟨c0, c1, hNonzero, hTopOrth⟩ :=
    p4Q2PZ37AMW_exists_twoMode_nonzero_originalPhysicalTopOrthogonal H beta hbeta
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let ρ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let w : Lp ℝ 2 μ :=
    ((c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
      c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) : Lp ℝ 2 μ)
  let J := p4Q2PZ37AMX_positiveTimeOneL2Pullback H
  let eval1 : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
    fun path => path (p4Q2PZ37AMX_positiveTimeOne H)
  have hwNe : w ≠ 0 := by
    intro hz
    apply hNonzero
    apply Subtype.ext
    simpa [w, μ] using hz
  have hJn : J w ≠ 0 := by
    intro hz
    have hnorm := J.norm_map w
    rw [hz, norm_zero] at hnorm
    exact hwNe (norm_eq_zero.mp hnorm.symm)
  have hMP : MeasurePreserving eval1 ρ μ :=
    p4Q2PZ37AMX_positiveTimeOne_measurePreserving H
  have hSource :
      w =ᵐ[μ]
        (fun A =>
          c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) +
          c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
    simpa [w, μ] using
      p4Q2PZ37AMW_twoMode_ae_originalSpatialWilsonObservable H c0 c1
  have hComp : J w =ᵐ[ρ] w ∘ eval1 := by
    exact Lp.coeFn_compMeasurePreserving w hMP
  have hPulled :
      w ∘ eval1 =ᵐ[ρ]
        (fun path =>
          c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 (eval1 path)) +
          c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 (eval1 path))) := by
    simpa [Function.comp_def] using hMP.quasiMeasurePreserving.ae_eq hSource
  refine ⟨c0, c1, hTopOrth, ?_, ?_⟩
  · simpa [J, w, μ] using hJn
  · simpa [J, w, μ, ρ, eval1] using hComp.trans hPulled

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMX_positiveTimeOne_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMX_exists_nonzero_oneStepPositiveHalfWilsonCylinder
