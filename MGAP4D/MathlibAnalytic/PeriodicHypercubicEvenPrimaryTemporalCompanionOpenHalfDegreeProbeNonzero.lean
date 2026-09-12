import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryTemporalCompanionOpenPathCoordinates
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullbackL2
import Mathlib.MeasureTheory.Measure.OpenPos

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProduct InnerProductSpace ENNReal

noncomputable section

private theorem primaryTemporalCompanionOpenHalfProbeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance primaryTemporalCompanionOpenHalfProbeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance primaryTemporalCompanionOpenHalfProbeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance primaryTemporalCompanionOpenHalfProbeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance primaryTemporalCompanionOpenHalfProbeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance primaryTemporalCompanionOpenHalfProbeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance primaryTemporalCompanionOpenHalfProbeHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance primaryTemporalCompanionOpenHalfProbeOpenHalfHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  unfold periodicHypercubicEvenOpenHalfHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
  infer_instance

/-- The cyclic holonomy formed from the four actual primary temporal companions
is continuous on the genuine positive-open-half configuration space. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy_continuous
    (H : ℕ) (hH : 0 < H) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
        H 2) := by
  let leg := fun k : Fin 4 =>
    fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)
  have hleg (k : Fin 4) : Continuous (leg k) := by
    simpa [leg] using
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionFiberedOpenPath_continuous
        H 2 hH k
  have hword : Continuous
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
        (leg 2 x)⁻¹ * (leg 3 x)⁻¹ * leg 0 x * leg 1 x) :=
    (((hleg 2).inv.mul (hleg 3).inv).mul (hleg 0)).mul (hleg 1)
  have hfun :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
          H 2 =
        (fun x => (leg 2 x)⁻¹ * (leg 3 x)⁻¹ * leg 0 x * leg 1 x) := by
    funext x
    unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
    rw [haarFinFourCyclicPlaquetteWord_eq]
  rw [hfun]
  exact hword

/-- The degree-`n` actual open-half normalized-trace feature is continuous. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature_continuous
    (H n : ℕ) (hH : 0 < H) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
        H n).feature := by
  let C :=
    (specialUnitaryNormalizedTraceRelativeKernelFeature
      2 primaryTemporalCompanionOpenHalfProbeTwoRankPositive).pow n
  have hKernel : Continuous fun p :
      Matrix.specialUnitaryGroup (Fin 2) ℂ ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      specialUnitaryNormalizedTraceRelativeKernel 2 p.1 p.2 ^ n :=
    (continuous_specialUnitaryNormalizedTraceRelativeKernel 2).pow n
  have hC : Continuous C.feature :=
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C hKernel
  have hHol :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy_continuous
      H hH
  simpa [C,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature,
    RealHilbertKernelFeature.comap] using hC.comp hHol

/-- Every transported scalar dual probe is continuous on the actual open-half
configuration space. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_continuous
    (H n : ℕ) (hH : 0 < H)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q) := by
  let q' :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
      H n q
  have hFeature :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature_continuous
      H n hH
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe,
    q'] using
    (innerSL ℝ q').continuous.comp hFeature

/-- The actual section associated with a boundary configuration reproduces the
same degree-feature scalar pairing.  The proof uses only the exact section
identity for the cyclic holonomy and the fact that boundary and open-half
features are two comaps of the same Hilbert feature. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_section_eq_boundary_inner
    (H n : ℕ) (hH : 0 < H)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H hH
          (fun k => b
            (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) =
      inner ℝ q
        ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H n).feature b) := by
  let x :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      H hH
      (fun k => b
        (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))
  have hHol :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
          H 2 x =
        periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b := by
    calc
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
          H 2 x =
        haarFinFourCyclicPlaquetteWord
          (fun k => b
            (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k)) := by
              exact
                periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy_section
                  H 2 hH
                  (fun k => b
                    (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))
      _ = periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b := by
        rfl
  have hProbeVector :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
          H n q = q := by
    rfl
  have hFeature :
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
          H n).feature x =
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H n).feature b := by
    let C :=
      (specialUnitaryNormalizedTraceRelativeKernelFeature
        2 primaryTemporalCompanionOpenHalfProbeTwoRankPositive).pow n
    change C.feature
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
          H 2 x) =
      C.feature
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b)
    rw [hHol]
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
  rw [hProbeVector, hFeature]
  rfl

/-- A nonzero boundary feature pairing yields a pointwise nonzero actual
open-half probe by evaluating at the explicit temporal-companion section. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_exists_ne_zero_of_boundary_inner_ne_zero
    (H n : ℕ) (hH : 0 < H)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (hb : inner ℝ q
      ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).feature b) ≠ 0) :
    ∃ x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ),
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q x ≠ 0 := by
  refine ⟨
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      H hH
      (fun k => b
        (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k)), ?_⟩
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_section_eq_boundary_inner
      H n hH q b]
  exact hb

/-- A pointwise nonzero continuous actual probe cannot represent the zero
vector in open-half Haar `L²`: normalized product Haar has full topological
support (`IsOpenPosMeasure`). -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_ne_zero_of_boundary_inner_ne_zero
    (H n : ℕ) (hH : 0 < H)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (hb : inner ℝ q
      ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).feature b) ≠ 0) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q ≠ 0 := by
  let μ := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let x :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      H hH
      (fun k => b
        (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))
  have hPoint :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q x ≠ 0 := by
    simpa [x] using
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_section_eq_boundary_inner
        H n hH q b).trans_ne hb
  have hContinuous :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_continuous
      H n hH q
  intro hZero
  have hRep :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_coeFn
      H n q
  rw [hZero] at hRep
  have hZeroRep :
      ((0 : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) :
          (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) → ℝ) =ᵐ[
        periodicHypercubicEvenOpenHalfHaarMeasure H 2]
        (fun _ => (0 : ℝ)) := by
    exact Filter.Eventually.of_forall (fun y => by simp)
  have hAE :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
          H n q =ᵐ[μ]
        (fun _ => (0 : ℝ)) := by
    exact hRep.symm.trans (by simpa [μ] using hZeroRep)
  have hEverywhere :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
          H n q =
        (fun _ => (0 : ℝ)) :=
    (hContinuous.ae_eq_iff_eq μ continuous_const).mp hAE
  exact hPoint (by simpa [x] using congrFun hEverywhere x)

/-- A nonzero weighted boundary q-moment already forces the same q to define a
nonzero actual open-half Haar `L²` probe.  No canonical choice of q is needed:
if q were orthogonal to every degree feature, the weighted scalar integrand
would vanish identically and so would its integral. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_ne_zero_of_weighted_boundary_integral_ne_zero
    (H n : ℕ) (hH : 0 < H)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (μ : Measure (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2))
    (p : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ)
    (hq :
      (∫ b, inner ℝ q
        (p b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
            H n).feature b) ∂μ) ≠ 0) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q ≠ 0 := by
  have hExists : ∃ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
      inner ℝ q
        ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H n).feature b) ≠ 0 := by
    by_contra hNo
    have hAll : ∀ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
        inner ℝ q
          ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
            H n).feature b) = 0 := by
      intro b
      by_contra hb
      exact hNo ⟨b, hb⟩
    apply hq
    have hFun :
        (fun b => inner ℝ q
          (p b •
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
              H n).feature b)) =
          (fun _ => (0 : ℝ)) := by
      funext b
      rw [real_inner_smul_right, hAll b, mul_zero]
    rw [hFun]
    simp
  rcases hExists with ⟨b, hb⟩
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_ne_zero_of_boundary_inner_ne_zero
      H n hH q b hb

end

end MathlibAnalytic
end MGAP4D