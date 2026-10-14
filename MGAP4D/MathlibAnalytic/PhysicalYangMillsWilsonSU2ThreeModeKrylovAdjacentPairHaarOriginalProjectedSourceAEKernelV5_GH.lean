import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSourceProjectionDetectionCriterionV5_GF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalActualAdjacentKrylovSourceProjectionV5_GG
import Mathlib.Tactic

/-!
# P4-Q2-GH — the physical source detection kernel in original pair-Haar a.e. form

The original Wilson signed physical receiver response of FF/FG and the
distinct pair-Haar outer reference are never confused here.

GD proves that the actual source/pseudodensity-contrast projection
alpha_{beta,e,f}(z) is measurable and its square pair-Haar integrable,
using a genuine Wilson conditional RMS domination, for beta>0.

Consequently the actual projected link mass integral is zero IFF
alpha=0 pair-Haar-a.e.; the finite physical patch mass is zero IFF
this holds for EVERY genuine link in that patch. These statements
do not rely on evaluating a single Haar atom.

GF's original physical Gram-null implies that ALL genuine link-source
posterior-contrast projections vanish almost everywhere. Conversely
a single link carrying a not-a.e.-zero physical projection ensures a
strictly positive original Gram Rayleigh, with the complete real
physical source sum retained.

The existence of such a physical source/link witness is not asserted,
nor is a source-frame constant, H-uniform summability, H1-C3 closure
or a continuum Yang–Mills mass gap. The original signed interacting
Wilson posterior remains the INNER law throughout.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

private noncomputable instance p4Q2GH_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- At positive beta the source-sensitive genuine Wilson posterior
contrast projection has zero actual integrated link mass iff its
continuous-physical-source coefficient vanishes pair-Haar almost everywhere.
The key integrability hypothesis was proved (not postulated) in GD. -/
theorem p4Q2GH_originalWilsonSourceProjectedLinkMean_zero_iff_ae
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
        H beta (le_of_lt hbeta) f e = 0 ↔
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
          H beta (le_of_lt hbeta) f e z = 0 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let alpha := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e
  have hInt : Integrable (fun z => (alpha z) ^ 2) μ := by
    simpa only [alpha, μ] using
      (p4Q2GD_originalPhysicalSourceProjection_sq_integrable H beta hbeta f e)
  have hNonneg : ∀ᵐ z ∂μ, 0 ≤ (alpha z) ^ 2 :=
    Filter.Eventually.of_forall (fun z => sq_nonneg (alpha z))
  have hIntegral :
      (∫ z, (alpha z) ^ 2 ∂μ) = 0 ↔
        (fun z => (alpha z) ^ 2) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
    integral_eq_zero_iff_of_nonneg_ae hNonneg hInt
  change (∫ z, (alpha z) ^ 2 ∂μ) = 0 ↔
    (∀ᵐ z ∂μ, alpha z = 0)
  constructor
  · intro hZero
    have hAE := hIntegral.mp hZero
    filter_upwards [hAE] with z hz
    have hSq : (alpha z) ^ 2 = 0 := hz
    exact sq_eq_zero_iff.mp hSq
  · intro hAE
    apply hIntegral.mpr
    filter_upwards [hAE] with z hz
    simp [hz]

/-- Exact finite original spatial patch kernel is the intersection of
the actually measured signed physical source-contrast a.e. kernels.
No assumed independence or physical source frame enters this equivalence. -/
theorem p4Q2GH_originalWilsonProjectedPatch_zero_iff_ae_allLinks
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
      H beta (le_of_lt hbeta) f S = 0 ↔
      ∀ e ∈ S,
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
          p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
            H beta (le_of_lt hbeta) f e z = 0 := by
  rw [p4Q2GF_originalWilsonProjectedPatch_zero_iff_allLinks_zero]
  constructor
  · intro h e he
    exact (p4Q2GH_originalWilsonSourceProjectedLinkMean_zero_iff_ae
      H beta hbeta f e).mp (h e he)
  · intro h e he
    exact (p4Q2GH_originalWilsonSourceProjectedLinkMean_zero_iff_ae
      H beta hbeta f e).mpr (h e he)

/-- A zero Gram Rayleigh for the genuine signed physical source
forces its original SU2 Wilson density-contrast receiver projection
to vanish for every physical spatial link, pair-Haar almost everywhere. -/
theorem p4Q2GH_originalWilsonGram_zero_implies_allLinkAEObstruction
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ)
    (hZero : star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
        beta (le_of_lt hbeta)
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver
          H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) = 0) :
    ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H),
      ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i) e z = 0 := by
  have hPatch :=
    p4Q2GF_originalWilsonGram_zero_implies_projectedSource_zero
      H beta hbeta f a hZero
  have hAE := (p4Q2GH_originalWilsonProjectedPatch_zero_iff_ae_allLinks
      H beta hbeta (∑ i : ι, a i • f i)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))).mp hPatch
  intro e
  exact hAE e (Finset.mem_univ e)

/-- A single true physical spatial link with a source contrast that does
NOT vanish pair-Haar-a.e. is sufficient for strict original Wilson Gram
Rayleigh positivity. The witness belongs to the ACTUAL signed source sum;
no point-Haar atom or hypothetical uniform source-frame is used. -/
theorem p4Q2GH_originalWilsonPhysicalGram_pos_of_oneLink_notAEZero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDetect : ¬ ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
      p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) (∑ i : ι, a i • f i) e z = 0) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H 2 (by norm_num) beta (le_of_lt hbeta)
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver
          H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  let F := ∑ i : ι, a i • f i
  let S : Finset (PeriodicHypercubicEvenSpatialSliceLink H) := Finset.univ
  have hLinkNe :
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
        H beta (le_of_lt hbeta) F e ≠ 0 := by
    intro hZero
    exact hDetect ((p4Q2GH_originalWilsonSourceProjectedLinkMean_zero_iff_ae
      H beta hbeta F e).mp hZero)
  have hPatchNe :
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        H beta (le_of_lt hbeta) F S ≠ 0 := by
    intro hZero
    have hall := (p4Q2GF_originalWilsonProjectedPatch_zero_iff_allLinks_zero
      H beta (le_of_lt hbeta) F S).mp hZero
    exact hLinkNe (hall e (Finset.mem_univ e))
  have hPatchNonneg :=
    p4Q2GF_originalWilsonSourceProjectedSpatialMass_nonneg
      H beta (le_of_lt hbeta) F S
  have hPatchPos : 0 <
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        H beta (le_of_lt hbeta) F S :=
    lt_of_le_of_ne hPatchNonneg (Ne.symm hPatchNe)
  exact p4Q2GF_originalWilsonPhysicalGram_pos_of_projectedSource_pos
    H beta hbeta f a hPatchPos

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GH_originalWilsonSourceProjectedLinkMean_zero_iff_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GH_originalWilsonProjectedPatch_zero_iff_ae_allLinks
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GH_originalWilsonGram_zero_implies_allLinkAEObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GH_originalWilsonPhysicalGram_pos_of_oneLink_notAEZero
