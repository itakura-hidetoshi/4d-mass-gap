import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalUnitGINGapNonzeroLeftBoundaryV5_LB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonPhysicalSourceGIBridgeV5_JU
import Mathlib.Tactic

/-!
# P4-Q2-LC — general TRUE Gauss-law physical source left-link factorization

LB proved the true finite-volume GI nonzero gap for the physical
constant unit. The kernel structure KZ depends ONLY on the genuine
Perron joint half-density, not on that unit. We now transport it to
EVERY true Gauss-law physical Hilbert source f, retaining the original
Wilson transfer integral of f without replacing it by an auxiliary
continuous test.

For a frozen right boundary R, left background L0, and actual physical
link e, the authentic JQ receiver is

  F_f(L0[e:=u],R[e:=g]) =
     ||T_b||^{-2} * (T_b f)(R[e:=g]) *
     C_b(u) * A_b(g) * exp(-b/4 <Phi(u),Phi(g)>).

For a fixed u0, multiplication by the TRUE interacting-posterior
density contrast and the inverse reference exponential gives a
CONTINUOUS right-link source ψ_f. Its nonvanishing at identity is
equivalent to nonvanishing of the ORIGINAL transfer integral there,
because KF, KZ and the actual transfer norm are positive.

The exact signed-posterior GI test for f is consequently C(u)/C(u0)
times the negative-feature exponential transform of ψ_f. LA's
already-proved injectivity yields some genuine left boundary with
a nonzero original GI gap whenever that concrete original transfer
value is nonzero.

Finally instantiate the ACTUAL anchored centered spatial Wilson
physical source of JU and reduce the static two-context determinant to
that SAME named physical transfer condition. This is not a rank/frame
assumption, but an explicit remaining theorem obligation.

No independent Haar posterior, synthetic transfer, sorry/admit,
new axiom, global finite-volume transfer injectivity, H1-C3 or
continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num)

/-- EXACT original physical GI receiver for any true Gauss-law
Hilbert source, with the SAME true frozen Wilson transfer and
Perron positive joint half-density of GN/JQ/KZ. -/
theorem p4Q2LC_originalPhysicalSourceReceiver_leftBoundary_factorization
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (h u g : Gauge) :
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e
        (Function.update left₀ e u, right) g =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b hb‖⁻¹ ^ 2 *
        decomposableOneSliceTransferIntegral H 2 b f
          (Function.update right e g) *
        (p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u *
          p4Q2KZ_originalRightLinkScale H b hb left₀ right e g *
          Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g))) := by
  rw [p4Q2JQ_originalPhysicalSourceLinkReceiver_apply,
    p4Q2GN_originalReceiver_eq_transferIntegral]
  rw [div_eq_mul_inv,
    p4Q2KZ_originalLeftBoundaryInverseHalfDensity_factorization
      H b hb left₀ right e h u g]
  ring

/-- Real continuous source derived from the ACTUAL JQ physical receiver
for f at a fixed genuine reference left link u0 and the true
two-interacting-Wilson-posterior density contrast. -/
noncomputable def p4Q2LC_originalPhysicalSignedCompensatedRightSource
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (u₀ : Gauge) : C(Gauge, ℝ) := by
  let F₀ : C(Gauge, ℝ) :=
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e
      (Function.update left₀ e u₀, right)
  let D : Gauge → ℝ :=
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e
  have hExp :
      Continuous (fun g : Gauge =>
        Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))) := by
    have hE : Continuous (fun g : Gauge =>
        p4Q2KR_originalSU2FeatureExponentialContinuous (b / 4) (u₀, g)) :=
      (p4Q2KR_originalSU2FeatureExponentialContinuous (b / 4)).continuous.comp
        (continuous_const.prodMk continuous_id)
    simpa only [p4Q2KR_originalSU2FeatureExponentialContinuous_apply] using hE
  exact ⟨fun g => F₀ g * D g *
      Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)),
    (F₀.continuous.mul
      (p4Q2GN_originalDensityContrast_continuous H b hb right e)).mul hExp⟩

@[simp] theorem p4Q2LC_originalPhysicalSignedCompensatedRightSource_apply
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (u₀ g : Gauge) :
    p4Q2LC_originalPhysicalSignedCompensatedRightSource
      H b hb f left₀ right e u₀ g =
      p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e
        (Function.update left₀ e u₀, right) g *
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g *
      Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) := rfl

/-- An actual physical source whose true frozen Wilson transfer
does not vanish at the identity right-link fiber has nonzero
compensated signed source. The required premise is precisely the
ORIGINAL transfer-integral value; no source-rank surrogate. -/
theorem p4Q2LC_originalPhysicalSignedSource_ne_zero_of_transfer_identity
    (b : ℝ) (hb : 0 < b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (u₀ : Gauge)
    (ht : decomposableOneSliceTransferIntegral H 2 b f
        (Function.update right e (1 : Gauge)) ≠ 0) :
    p4Q2LC_originalPhysicalSignedCompensatedRightSource
      H b hb.le f left₀ right e u₀ ≠ 0 := by
  have hL :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b hb.le‖⁻¹ ≠ 0 :=
    inv_ne_zero
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) b hb.le).ne'
  have hs :
      continuousJointSqrtDensity H 2 (by norm_num) b hb.le
        (Function.update left₀ e u₀,
          Function.update right e (1 : Gauge)) ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb.le
      (Function.update left₀ e u₀, Function.update right e 1)).ne'
  have hF :
      p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le f e
        (Function.update left₀ e u₀, right) (1 : Gauge) ≠ 0 := by
    rw [p4Q2JQ_originalPhysicalSourceLinkReceiver_apply,
      p4Q2GN_originalReceiver_eq_transferIntegral]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hL) ht) hs
  have hD :=
    (p4Q2KF_originalPosteriorDensityContrast_identity_pos H b hb right e).ne'
  have hVal :
      p4Q2LC_originalPhysicalSignedCompensatedRightSource
        H b hb.le f left₀ right e u₀ (1 : Gauge) ≠ 0 := by
    rw [p4Q2LC_originalPhysicalSignedCompensatedRightSource_apply]
    exact mul_ne_zero (mul_ne_zero hF hD) (Real.exp_pos _).ne'
  intro hz
  apply hVal
  rw [hz]
  simp

/-- Exact original GI TEST for every physical f as the same
negative-exponential Haar transform proved injective in LA. -/
theorem p4Q2LC_originalPhysicalPosteriorTestGap_factorization
    (b : ℝ) (hb : 0 ≤ b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (h u₀ u : Gauge) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e
      (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e
        (Function.update left₀ e u, right)) =
      (p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u /
        p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u₀) *
      (∫ g : Gauge,
        Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) *
          p4Q2LC_originalPhysicalSignedCompensatedRightSource
            H b hb f left₀ right e u₀ g ∂nu) := by
  let F : Gauge → C(Gauge, ℝ) := fun v =>
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb f e
      (Function.update left₀ e v, right)
  let D : Gauge → ℝ :=
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e
  let C : Gauge → ℝ :=
    p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h
  let A : Gauge → ℝ :=
    p4Q2KZ_originalRightLinkScale H b hb left₀ right e
  let N : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ ^ 2
  let M : Gauge → ℝ := fun g =>
    decomposableOneSliceTransferIntegral H 2 b f
      (Function.update right e g)
  let E : Gauge → Gauge → ℝ := fun v g =>
    Real.exp (-(b / 4) * inner ℝ (Phi v) (Phi g))
  let ψ : C(Gauge, ℝ) :=
    p4Q2LC_originalPhysicalSignedCompensatedRightSource
      H b hb f left₀ right e u₀
  have hC₀ : C u₀ ≠ 0 :=
    (p4Q2KZ_originalLeftBoundaryScale_pos
      H b hb left₀ right e h u₀).ne'
  have hFu (v g : Gauge) :
      F v g = N * M g * (C v * A g * E v g) :=
    p4Q2LC_originalPhysicalSourceReceiver_leftBoundary_factorization
      H b hb f left₀ right e h v g
  have hEcancel (g : Gauge) :
      E u₀ g *
        Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) = 1 := by
    dsimp [E]
    rw [← Real.exp_add]
    have hArg :
        -(b / 4) * inner ℝ (Phi u₀) (Phi g) +
          (b / 4) * inner ℝ (Phi u₀) (Phi g) = 0 := by ring
    rw [hArg, Real.exp_zero]
  have hReference (g : Gauge) :
      F u₀ g * Real.exp ((b / 4) *
          inner ℝ (Phi u₀) (Phi g)) =
        N * M g * (C u₀ * A g) := by
    rw [hFu u₀ g]
    calc
      N * M g * (C u₀ * A g * E u₀ g) *
          Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) =
        (N * M g * (C u₀ * A g)) *
          (E u₀ g * Real.exp ((b / 4) *
            inner ℝ (Phi u₀) (Phi g))) := by ring
      _ = N * M g * (C u₀ * A g) := by
        rw [hEcancel g]
        ring
  have hPoint (g : Gauge) :
      F u g * D g = (C u / C u₀) * (E u g * ψ g) := by
    rw [p4Q2LC_originalPhysicalSignedCompensatedRightSource_apply]
    change F u g * D g =
      (C u / C u₀) *
        (E u g * ((F u₀ g * D g) *
          Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))))
    calc
      F u g * D g =
          (N * M g * (C u * A g * E u g)) * D g := by
        rw [hFu]
      _ = (C u / C u₀) *
          (E u g * ((N * M g * (C u₀ * A g)) * D g)) := by
        field_simp [hC₀]
        try ring
      _ = (C u / C u₀) *
          (E u g * ((F u₀ g *
            Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g))) * D g)) := by
        rw [hReference]
      _ = _ := by ring
  change (∫ g : Gauge, F u g * D g ∂nu) =
    (C u / C u₀) * (∫ g : Gauge, E u g * ψ g ∂nu)
  calc
    (∫ g : Gauge, F u g * D g ∂nu) =
        ∫ g : Gauge, (C u / C u₀) *
          (E u g * ψ g) ∂nu := by
      apply integral_congr_ae
      filter_upwards with g
      exact hPoint g
    _ = (C u / C u₀) * (∫ g : Gauge, E u g * ψ g ∂nu) :=
      integral_const_mul _ _

/-- Every true physical f with a nonzero original right-fiber
Wilson transfer at identity is genuinely GI-detected in SOME
actual left boundary after the standard physical JQ normalization. -/
theorem p4Q2LC_originalPhysicalGI_nonzero_some_left_of_transfer_identity
    (b : ℝ) (hb : 0 < b) (f : Phys)
    (left₀ right : Cfg) (e : Link) (h u₀ : Gauge)
    (ht : decomposableOneSliceTransferIntegral H 2 b f
        (Function.update right e (1 : Gauge)) ≠ 0) :
    ∃ u : Gauge,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e (Function.update left₀ e u, right) ≠ 0 := by
  let ψ : C(Gauge, ℝ) :=
    p4Q2LC_originalPhysicalSignedCompensatedRightSource
      H b hb.le f left₀ right e u₀
  have hψ : ψ ≠ 0 :=
    p4Q2LC_originalPhysicalSignedSource_ne_zero_of_transfer_identity
      H b hb f left₀ right e u₀ ht
  obtain ⟨u, hu⟩ :=
    p4Q2LA_originalNegativeExponentialHaarTransform_exists_nonzero_receiver
      b hb ψ hψ
  refine ⟨u, ?_⟩
  have hC : 0 <
      p4Q2KZ_originalLeftBoundaryScale H b hb.le left₀ right e h u /
      p4Q2KZ_originalLeftBoundaryScale H b hb.le left₀ right e h u₀ :=
    div_pos
      (p4Q2KZ_originalLeftBoundaryScale_pos H b hb.le left₀ right e h u)
      (p4Q2KZ_originalLeftBoundaryScale_pos H b hb.le left₀ right e h u₀)
  have hTest :
      p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb.le right e
        (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le f e
          (Function.update left₀ e u, right)) ≠ 0 := by
    rw [p4Q2LC_originalPhysicalPosteriorTestGap_factorization
      H b hb.le f left₀ right e h u₀ u]
    exact mul_ne_zero hC.ne' hu
  have hQ :
      p4Q2JQ_originalPhysicalGIDensityWeight H b hb.le
        (Function.update left₀ e u, right) ≠ 0 :=
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos H b hb.le
      (Function.update left₀ e u, right)).ne'
  rw [p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div]
  exact div_ne_zero (neg_ne_zero.mpr hTest) hQ

/-- Concrete KZ/LA/LC-to-JU bridge for the actual anchor-centered
spatial Wilson physical Hilbert source. The only remaining input
is the original Wilson transfer integral at a named right-link
identity configuration, not a detector-rank or source-frame axiom. -/
theorem p4Q2LC_originalSpatialWilsonMinor_nonzero_of_centeredTransfer_identity
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (z : Cfg × Cfg) (left₀ right : Cfg) (h u₀ : Gauge)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
          ℝ (1 : C(Cfg, ℝ))) ≠ 0)
    (ht :
      decomposableOneSliceTransferIntegral H 2 b
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
          H b hb.le e z) (Function.update right e' (1 : Gauge)) ≠ 0) :
    ∃ u : Gauge,
      p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z
        (Function.update left₀ e' u, right) ≠ 0 := by
  obtain ⟨u, hu⟩ :=
    p4Q2LC_originalPhysicalGI_nonzero_some_left_of_transfer_identity
      H b hb
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
      left₀ right e' h u₀ ht
  refine ⟨u, ?_⟩
  exact (p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne
    H b hb.le e e' z (Function.update left₀ e' u, right) hAnchor).2 hu

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LC_originalPhysicalSourceReceiver_leftBoundary_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LC_originalPhysicalSignedCompensatedRightSource_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LC_originalPhysicalSignedSource_ne_zero_of_transfer_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LC_originalPhysicalPosteriorTestGap_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LC_originalPhysicalGI_nonzero_some_left_of_transfer_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LC_originalSpatialWilsonMinor_nonzero_of_centeredTransfer_identity
