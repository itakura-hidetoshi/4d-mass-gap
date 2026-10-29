import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIMomentStrictPosV5_PZ37ABA2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointBoundaryContinuityV5_HI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABB — true Wilson open pair-Haar GI signal event

AAZ proved: for every actual finite-volume SU(2) Wilson model H,b>0,
some genuine spatial link e has NON-a.e.-zero original centered
Gauss-law signed two-interacting-posterior GI expectation difference.
HI independently proved the SAME physical expectation difference
continuous in the COMPLETE original pair of boundary configurations.

This module constructs a genuine NONEMPTY OPEN full pair-Haar event E,
a strictly positive numeric gap threshold delta_H,b, and proves
  0 < pairHaar(E), and
  delta_H,b <= |genuine centered GI two-posterior gap(z)| on E.
This is a quantitative local statement for every finite H,b:
no point-mass fictitious Haar atom, no arbitrary substitute posterior.

Moreover the ORIGINAL UNWEIGHTED second moment is bounded below by the
strictly positive actual real Haar event mass times delta_H,b^2.
Thus finite-volume positive Haar mass and noncancelling physical GI
amplitude are constructed from Wilson rather than hypothesized.

IMPORTANT: The event E and delta_H,b and real mass rho_H,b depend on H,b.
E is an open event on the true *finite* pair configuration carrier;
this does NOT claim its dependence is restricted to a common finite set
of links as H varies, nor any uniform lower bound on its Haar mass.
Constructing a fixed-support cylinder and H-uniform delta/rho remains
an independent analytic obstacle. No new axioms/sorry/admit/native_decide,
unphysical measure, altered source or conditional posterior, common fine
interval, E/F, H1-H4, or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABB_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABB_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABB_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABB_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABB_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ABB_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37ABB_haarOpenPos :
    (normalizedCompactHaar G).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2PZ37ABB_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ABB_pairHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- A genuine positive-mass open *original pair-Haar* event and a
positive absolute signed GI-gap threshold are automatic for EACH
actual finite H and b>0; the event is not yet a uniform cylinder. -/
theorem p4Q2PZ37ABB_exists_originalOpenPairHaarEvent_positiveGIGap
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
      (delta : ℝ),
      0 < delta ∧ IsOpen E ∧
      0 < periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 E ∧
      ∀ z ∈ E,
        delta ≤ |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z| := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  obtain ⟨e, hNotAE⟩ :=
    p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero H b hb
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  have hDNotAE : ¬ (∀ᵐ z ∂μ, D z = 0) := hNotAE
  have hPoint : ∃ z0 : Pair, D z0 ≠ 0 := by
    by_contra hn
    apply hDNotAE
    have hz : ∀ z : Pair, D z = 0 := by
      intro z
      by_contra hne
      exact hn ⟨z, hne⟩
    filter_upwards with z
    exact hz z
  obtain ⟨z0, hz0⟩ := hPoint
  have hCont : Continuous D :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e
  let delta : ℝ := |D z0| / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact half_pos (abs_pos.mpr hz0)
  let E : Set Pair := {z | delta < |D z|}
  have hOpen : IsOpen E := by
    change IsOpen ((fun z : Pair => |D z|) ⁻¹' Set.Ioi delta)
    exact isOpen_Ioi.preimage hCont.abs
  have hz0E : z0 ∈ E := by
    change delta < |D z0|
    dsimp [delta]
    have hPos : 0 < |D z0| := abs_pos.mpr hz0
    linarith
  have hMass : 0 < μ E := hOpen.measure_pos μ ⟨z0, hz0E⟩
  refine ⟨e, E, delta, hdelta, hOpen, hMass, ?_⟩
  intro z hz
  change delta < |D z| at hz
  exact hz.le

/-- Strictly positive *real* original pair-Haar event mass and the
actual unweighted GI squared moment lower certificate, at fixed H,b.
The genuine FX cap and automatic original integrability are provided
by ABA and AAZ2, so no extra integrability premise occurs. -/
theorem p4Q2PZ37ABB_exists_originalOpenEvent_positiveMassMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
      (delta rho : ℝ),
      0 < delta ∧ 0 < rho ∧ IsOpen E ∧
      (rho = (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).real E) ∧
      (∀ z ∈ E,
        delta ≤ |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z|) ∧
      rho * delta^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  obtain ⟨e, E, delta, hdelta, hOpen, hPos, hGap⟩ :=
    p4Q2PZ37ABB_exists_originalOpenPairHaarEvent_positiveGIGap H b hb
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let rho : ℝ := μ.real E
  have hrho : 0 < rho := by
    change 0 < (μ E).toReal
    exact ENNReal.toReal_pos hPos.ne' (measure_ne_top μ E)
  have hQCap : ∀ z : Pair,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤
        (Real.exp (16 * b) - Real.exp (-16 * b)) ^ 2 := by
    intro z
    exact p4Q2PZ37ABA_originalFXVariance_le_FK_envelope
      H b hb.le z.2 e
  have hDInt : Integrable (fun z : Pair => (D z)^2) μ := by
    change Integrable
      (fun z : Pair =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    exact p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
      H b hb e ((Real.exp (16 * b) - Real.exp (-16 * b)) ^ 2) hQCap
  have hIndicatorInt :
      Integrable (fun z : Pair => E.indicator (fun _ : Pair => delta^2) z) μ :=
    (integrable_const (delta^2 : ℝ)).indicator hOpen.measurableSet
  have hPointwise (z : Pair) :
      E.indicator (fun _ : Pair => delta^2) z ≤ (D z)^2 := by
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      have hAbs : delta ≤ |D z| := hGap z hz
      have hSq := pow_le_pow_left₀ hdelta.le hAbs 2
      simpa only [sq_abs] using hSq
    · have hIndicatorZero :
          E.indicator (fun _ : Pair => delta^2) z = 0 := by
        simp [hz]
      rw [hIndicatorZero]
      exact sq_nonneg _
  have hIntegral :
      (∫ z : Pair, E.indicator (fun _ : Pair => delta^2) z ∂μ) ≤
        ∫ z : Pair, (D z)^2 ∂μ := by
    apply integral_mono hIndicatorInt hDInt
    exact hPointwise
  have hIndicator :
      (∫ z : Pair, E.indicator (fun _ : Pair => delta^2) z ∂μ) =
        rho * delta^2 := by
    simpa only [rho, smul_eq_mul] using
      (integral_indicator_const (delta^2 : ℝ) hOpen.measurableSet
        (μ := μ))
  refine ⟨e, E, delta, rho, hdelta, hrho, hOpen, rfl, hGap, ?_⟩
  change rho * delta^2 ≤ ∫ z : Pair, (D z)^2 ∂μ
  exact hIndicator ▸ hIntegral

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABB_exists_originalOpenPairHaarEvent_positiveGIGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABB_exists_originalOpenEvent_positiveMassMoment
