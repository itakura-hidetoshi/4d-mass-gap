import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGISpatialActionMinorTangentV5_JI
import Mathlib.Tactic

/-!
# P4-Q2-JK: actual static spatial Wilson GI anchor, common kernel and Haar obstruction

We retain the ORIGINAL frozen interacting-Wilson two-posterior GI detectors
from JH and the ORIGINAL spatial Wilson action from JI. At a genuinely
nonzero zero-mode GI anchor, the original static two-context determinant
is precisely its nonzero value times ONE centered Wilson-action response.

The centered source is itself NONZERO in the original spatial Haar-L2
carrier by the actual SU(2) primary-plaquette central twist and full
support of normalized Haar. Its possible GI invisibility is therefore a
genuine detector obstruction, not an accidental zero source.

The common detector kernel is identified with the joint orthogonality
conditions against the actual JH Riesz representers, and the remaining
nonvanishing problem is expressed in ONE explicit original interacting
posterior Wilson-Haar iterated integral at a second genuine context.

NO nonzero second-context response is assumed/proved here. This file
does NOT prove a positive GL floor, H-uniform estimate, H1-C3 closure,
continuum Yang-Mills construction or mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2JK_SU2_normalizedHaarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2JK_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section Frozen

variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb
local notation "W" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "delta" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb

/-- The ratio of the TWO actual original GI responses at a selected
physical link and full left/right SU(2) boundary context. It is useful
only after the zero-mode anchor has been PROVED nonzero. -/
noncomputable def p4Q2JK_originalWilsonAnchorSlope
    (e : Link) (z : Cfg × Cfg) : ℝ :=
  G e z (L W) / G e z (L (1 : C(Cfg, ℝ)))

/-- The true continuous spatial Wilson action with its GI-anchor scalar
removed. No independent conditional posterior is involved. -/
noncomputable def p4Q2JK_anchorCenteredSpatialWilson
    (e : Link) (z : Cfg × Cfg) : C(Cfg, ℝ) :=
  W - p4Q2JK_originalWilsonAnchorSlope H b hb e z • (1 : C(Cfg, ℝ))

theorem p4Q2JK_centeredWilson_toLp
    (e : Link) (z : Cfg × Cfg) :
    L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) =
      L W - p4Q2JK_originalWilsonAnchorSlope H b hb e z •
        L (1 : C(Cfg, ℝ)) := by
  unfold p4Q2JK_anchorCenteredSpatialWilson
  rw [map_sub, map_smul]

/-- The genuine anchor annihilates its own centered Wilson direction. -/
theorem p4Q2JK_originalGI_anchor_annihilates_centeredWilson
    (e : Link) (z : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    G e z (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) = 0 := by
  rw [p4Q2JK_centeredWilson_toLp, map_sub, map_smul]
  simp only [smul_eq_mul]
  unfold p4Q2JK_originalWilsonAnchorSlope
  field_simp [hAnchor]
  ring

/-- The ORIGINAL two-context static GI minor is exactly one original
nonzero anchor times ONE actual centered Wilson response at y. -/
theorem p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' =
      G e z (L (1 : C(Cfg, ℝ))) *
        G e' z' (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) := by
  rw [p4Q2JK_centeredWilson_toLp, map_sub, map_smul]
  simp only [smul_eq_mul]
  unfold p4Q2JI_originalGISpatialActionMinor
    p4Q2JK_originalWilsonAnchorSlope
  field_simp [hAnchor]

theorem p4Q2JK_originalSpatialMinor_ne_iff_centeredGI_ne
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0 ↔
      G e' z' (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) ≠ 0 := by
  rw [p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI H b hb e e' z z' hAnchor]
  constructor
  · intro h hn
    apply h
    rw [hn, mul_zero]
  · exact mul_ne_zero hAnchor

/-- Full support of the REAL SU(2) spatial product Haar and IY's
actual central-link twist show that subtracting ANY anchor scalar
cannot erase the genuine nonconstant spatial Wilson source in L2. -/
theorem p4Q2JK_anchorCenteredSpatialWilson_HaarLp_ne_zero
    (e : Link) (z : Cfg × Cfg) :
    L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) ≠ 0 := by
  let c := p4Q2JK_originalWilsonAnchorSlope H b hb e z
  change L (W - c • (1 : C(Cfg, ℝ))) ≠ 0
  intro h0
  have hCont : W - c • (1 : C(Cfg, ℝ)) = 0 := by
    apply (ContinuousMap.toLp_injective (p := 2) (μ := haar) (𝕜 := ℝ))
    simpa only [map_zero] using h0
  obtain ⟨B₀, B₁, hW⟩ := p4Q2IY_originalSpatialWilsonAction_not_constant H
  have hc (B : Cfg) : W B = c := by
    have hc' : W = c • (1 : C(Cfg, ℝ)) := sub_eq_zero.mp hCont
    have h := congrArg (fun f : C(Cfg, ℝ) => f B) hc'
    simpa using h
  exact hW ((hc B₀).trans (hc B₁).symm)

/-- The actual intersection of all ORIGINAL interacting-Wilson GI
functional kernels, indexed over every real link/full SU(2) context. -/
noncomputable def p4Q2JK_originalGICommonKernel :
    Submodule ℝ (Lp ℝ 2 haar) :=
  ⨅ e : Link, ⨅ z : Cfg × Cfg, (G e z).ker

theorem p4Q2JK_mem_originalGICommonKernel_iff
    (v : Lp ℝ 2 haar) :
    v ∈ p4Q2JK_originalGICommonKernel H b hb ↔
      ∀ e : Link, ∀ z : Cfg × Cfg, G e z v = 0 := by
  simp [p4Q2JK_originalGICommonKernel]

/-- For an actual NONZERO original anchor, vanishing of EVERY static
spatial Wilson 2-context minor is exactly membership of the
nonzero centered original spatial action in the GI common kernel. -/
theorem p4Q2JK_allOriginalSpatialMinors_zero_iff_centered_mem_commonKernel
    (e : Link) (z : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    (∀ e' : Link, ∀ z' : Cfg × Cfg,
        p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' = 0) ↔
      L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) ∈
        p4Q2JK_originalGICommonKernel H b hb := by
  rw [p4Q2JK_mem_originalGICommonKernel_iff]
  constructor
  · intro h e' z'
    have hm := h e' z'
    rw [p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI
      H b hb e e' z z' hAnchor] at hm
    exact (mul_eq_zero.mp hm).resolve_left hAnchor
  · intro h e' z'
    rw [p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI
      H b hb e e' z z' hAnchor, h e' z', mul_zero]

theorem p4Q2JK_exists_nonzeroOriginalSpatialMinor_iff_centered_not_mem
    (e : Link) (z : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    (∃ e' : Link, ∃ z' : Cfg × Cfg,
        p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0) ↔
      L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) ∉
        p4Q2JK_originalGICommonKernel H b hb := by
  constructor
  · rintro ⟨e', z', hne⟩ hmem
    have hall :=
      (p4Q2JK_allOriginalSpatialMinors_zero_iff_centered_mem_commonKernel
        H b hb e z hAnchor).2 hmem
    exact hne (hall e' z')
  · intro hnot
    by_contra h
    push Not at h
    exact hnot
      ((p4Q2JK_allOriginalSpatialMinors_zero_iff_centered_mem_commonKernel
        H b hb e z hAnchor).1 h)

/-- The exact REAL Riesz representation of the ORIGINAL frozen GI
detector, including the genuine transfer norm and joint-density factor. -/
theorem p4Q2JK_originalGI_eq_actualRieszInner
    (e : Link) (z : Cfg × Cfg) (v : Lp ℝ 2 haar) :
    G e z v =
      (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ * s z) *
      inner ℝ (L (p4Q2JH_originalFiberRepresenter H b hb e z)) v := by
  rfl

theorem p4Q2JK_originalGIRieszPrefactor_ne_zero (z : Cfg × Cfg) :
    (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * s z) ≠ 0 := by
  have hT :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b hb).ne'
  have hs : s z ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb z).ne'
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hT)) hs

/-- All genuine GI functionals fail to see the centered source iff
all ACTUAL frozen Wilson Riesz representers are orthogonal to it. -/
theorem p4Q2JK_centered_mem_commonKernel_iff_RieszOrthogonal
    (e : Link) (z : Cfg × Cfg) :
    L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) ∈
      p4Q2JK_originalGICommonKernel H b hb ↔
    ∀ e' : Link, ∀ z' : Cfg × Cfg,
      inner ℝ (L (p4Q2JH_originalFiberRepresenter H b hb e' z'))
        (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) = 0 := by
  rw [p4Q2JK_mem_originalGICommonKernel_iff]
  constructor
  · intro h e' z'
    have hh := h e' z'
    rw [p4Q2JK_originalGI_eq_actualRieszInner] at hh
    exact (mul_eq_zero.mp hh).resolve_left
      (p4Q2JK_originalGIRieszPrefactor_ne_zero H b hb z')
  · intro h e' z'
    rw [p4Q2JK_originalGI_eq_actualRieszInner, h e' z', mul_zero]

/-- A SINGLE literal frozen-Wilson double Haar integral for a given
anchored and candidate second SU(2) link/boundary context. This still
contains the true JOINT square-root density and the TWO interacting
posterior densities through their original contrast. -/
noncomputable def p4Q2JK_originalCenteredWilsonHaarMoment
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  ∫ g : Gauge,
    ((∫ A : Cfg,
      K A (Function.update z'.2 e' g) *
        p4Q2JK_anchorCenteredSpatialWilson H b hb e z A ∂haar) /
        s (z'.1, Function.update z'.2 e' g)) *
      delta z'.2 e' g ∂nu

/-- Fubini's verified JH physical moment identity, WITHOUT changing
the interacting posterior to an independent Haar posterior. -/
theorem p4Q2JK_originalCenteredGI_eq_actualPosteriorHaarMoment
    (e e' : Link) (z z' : Cfg × Cfg) :
    G e' z' (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) =
      (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ * s z') *
        p4Q2JK_originalCenteredWilsonHaarMoment H b hb e e' z z' := by
  unfold p4Q2JK_originalCenteredWilsonHaarMoment
  change (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * s z') *
    p4Q2JH_originalFiberMomentCLM H b hb e' z'
      (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) = _
  rw [p4Q2JH_originalFiberMomentCLM_eq_iteratedIntegral]

/-- Entire ORIGINAL static Wilson GI determinant as a product of
two nonzero physical factors and ONE real interacting posterior Haar
moment. The last factor is the genuine unresolved detector input. -/
theorem p4Q2JK_originalSpatialMinor_eq_actualHaarMoment
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' =
      G e z (L (1 : C(Cfg, ℝ))) *
      ((-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b hb‖⁻¹ * s z') *
        p4Q2JK_originalCenteredWilsonHaarMoment H b hb e e' z z') := by
  rw [p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI
    H b hb e e' z z' hAnchor,
    p4Q2JK_originalCenteredGI_eq_actualPosteriorHaarMoment]

theorem p4Q2JK_originalSpatialMinor_ne_iff_actualHaarMoment_ne
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : G e z (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0 ↔
      p4Q2JK_originalCenteredWilsonHaarMoment H b hb e e' z z' ≠ 0 := by
  rw [p4Q2JK_originalSpatialMinor_eq_actualHaarMoment
    H b hb e e' z z' hAnchor]
  constructor
  · intro h hn
    apply h
    simp [hn]
  · intro h
    exact mul_ne_zero hAnchor
      (mul_ne_zero (p4Q2JK_originalGIRieszPrefactor_ne_zero H b hb z') h)

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_centeredWilson_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalGI_anchor_annihilates_centeredWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalSpatialMinor_ne_iff_centeredGI_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_anchorCenteredSpatialWilson_HaarLp_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_mem_originalGICommonKernel_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_allOriginalSpatialMinors_zero_iff_centered_mem_commonKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_exists_nonzeroOriginalSpatialMinor_iff_centered_not_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalGI_eq_actualRieszInner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalGIRieszPrefactor_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_centered_mem_commonKernel_iff_RieszOrthogonal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalCenteredGI_eq_actualPosteriorHaarMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalSpatialMinor_eq_actualHaarMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JK_originalSpatialMinor_ne_iff_actualHaarMoment_ne
