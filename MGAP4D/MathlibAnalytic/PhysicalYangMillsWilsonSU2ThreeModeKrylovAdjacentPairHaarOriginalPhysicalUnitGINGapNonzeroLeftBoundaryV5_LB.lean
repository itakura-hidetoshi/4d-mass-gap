import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2AntipodalNegativeExponentialInjectiveV5_LA
import Mathlib.Tactic

/-!
# P4-Q2-LB — TRUE physical constant-unit GI expectation-gap left-context detection

KY identified the original Perron joint half-density four-corner
exponential at beta/4. KZ factored the original physical constant-unit
receiver under varying only ONE genuine left SU(2) link as a left-positive
scalar times a fixed right-positive source and a NEGATIVE real feature
exponential. LA proved the actual negative feature exponential transform
is injective by SU(2)'s physical central pi-rotation and the already
established positive-beta Wilson transform injectivity KV.

Now construct one explicit NONZERO continuous signed right source from
the SAME genuine interacting two-Wilson-posterior density difference,
and the SAME genuine physical constant-unit transfer receiver.
Fix any reference left-link value u0 and compensate its feature
exponential pointwise. Source continuity uses KR's ACTUAL continuous
feature-exponential and JQ/GN's ACTUAL continuous receiver and density
contrast. The source is nonzero at SU(2) identity by KF and KX.

An exact right SU(2) Haar moment equality, retaining the true positive
Perron normalization, then transports LA's nonzero receiver to a
NONZERO ORIGINAL PHYSICAL GI EXPECTATION GAP at some actual left
boundary differing only on link e. This is an EXISTENTIAL,
pointwise, finite-volume/positive-beta detection statement for the
actual physical unit source; it does NOT prove the desired spatial
Wilson-centered two-context determinant, uniform in-volume lower bound,
H1-C3, OS reconstruction or continuum Yang-Mills mass gap.

No rank/source-frame hypothesis, independent-Haar posterior,
Dobrushin assumption, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2

/-- An EXPLICIT continuous source on the real SU(2) group. This is the
product of the ACTUAL two-interacting-Wilson-posterior density contrast
and the ACTUAL original physical unit receiver at a frozen left
reference value u0, compensated by the positive feature exponential.
Nothing is replaced by an independent-Haar posterior. -/
noncomputable def p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (u₀ : Gauge) : C(Gauge, ℝ) := by
  let F₀ : C(Gauge, ℝ) :=
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e
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

@[simp] theorem p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_apply
    (b : ℝ) (hb : 0 ≤ b) (left₀ right : Cfg)
    (e : Link) (u₀ g : Gauge) :
    p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
      H b hb left₀ right e u₀ g =
      p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e
        (Function.update left₀ e u₀, right) g *
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g *
      Real.exp ((b / 4) * inner ℝ (Phi u₀) (Phi g)) := rfl

/-- Genuine physical signed compensated source is NONZERO already at
identity, since BOTH the original physical unit receiver and the
actual interacting posterior contrast are strictly positive there. -/
theorem p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_ne_zero
    (b : ℝ) (hb : 0 < b) (left₀ right : Cfg)
    (e : Link) (u₀ : Gauge) :
    p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
      H b hb.le left₀ right e u₀ ≠ 0 := by
  have hF :=
    p4Q2KX_originalPhysicalUnitReceiver_pos
      H b hb.le e (Function.update left₀ e u₀, right) (1 : Gauge)
  have hD :=
    p4Q2KF_originalPosteriorDensityContrast_identity_pos
      H b hb right e
  have hAtIdentity :
      0 < p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
        H b hb.le left₀ right e u₀ (1 : Gauge) := by
    rw [p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_apply]
    exact mul_pos (mul_pos hF hD) (Real.exp_pos _)
  intro hZero
  have hAtZero :
      p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
        H b hb.le left₀ right e u₀ (1 : Gauge) = 0 := by
    rw [hZero]
    simp
  exact (ne_of_gt hAtIdentity) hAtZero

/-- The ORIGINAL signed interacting-posterior test of the ORIGINAL
physical unit receiver for the actual left link u is EXACTLY the
negative exponential Haar transform of the fixed LB nonzero source,
times the strictly positive original left scale C(u)/C(u0).

The reference u0 can be ANY actual SU(2) group element. The full
spatial Wilson kernel mass, joint Perron half-density and proper
normalization remain present through the imported KZ identities. -/
theorem p4Q2LB_originalPhysicalUnitPosteriorTestGap_factorization
    (b : ℝ) (hb : 0 ≤ b)
    (left₀ right : Cfg) (e : Link) (h u₀ u : Gauge) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e
      (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e
        (Function.update left₀ e u, right)) =
      (p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u /
        p4Q2KZ_originalLeftBoundaryScale H b hb left₀ right e h u₀) *
      (∫ g : Gauge,
        Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) *
          p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
            H b hb left₀ right e u₀ g ∂nu) := by
  let F : Gauge → C(Gauge, ℝ) := fun v =>
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e
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
    p4Q2KB_originalSpatialWilsonKernelMass H b (Function.update right e g)
  let E : Gauge → Gauge → ℝ := fun v g =>
    Real.exp (-(b / 4) * inner ℝ (Phi v) (Phi g))
  let ψ : C(Gauge, ℝ) :=
    p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
      H b hb left₀ right e u₀
  have hC₀ : C u₀ ≠ 0 :=
    (p4Q2KZ_originalLeftBoundaryScale_pos
      H b hb left₀ right e h u₀).ne'
  have hFu (v g : Gauge) :
      F v g = N * M g * (C v * A g * E v g) :=
    p4Q2KZ_originalPhysicalUnitReceiver_leftBoundary_factorization
      H b hb left₀ right e h v g
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
    rw [p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_apply]
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

/-- At EVERY finite original physical spatial volume and EVERY
positive coupling, any frozen right boundary and physical link
admits an ACTUAL left physical boundary differing from a chosen
reference only on that link, such that the TRUE ORIGINAL
GAUGE-INVARIANT PHYSICAL UNIT source's two-interacting-posterior
expectation gap is NONZERO.

This discharges the pointwise existential KX gap obstruction;
it is not an integrated a.e. source-frame lower bound, two-context
spatial Wilson determinant, or H1-C3 strong-limit closure. -/
theorem p4Q2LB_originalPhysicalUnitGI_nonzero_some_actualLeftBoundary
    (b : ℝ) (hb : 0 < b) (left₀ right : Cfg)
    (e : Link) (h u₀ : Gauge) :
    ∃ u : Gauge,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le U e
          (Function.update left₀ e u, right) ≠ 0 := by
  let ψ : C(Gauge, ℝ) :=
    p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource
      H b hb.le left₀ right e u₀
  have hψ : ψ ≠ 0 :=
    p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_ne_zero
      H b hb left₀ right e u₀
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
        (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le U e
          (Function.update left₀ e u, right)) ≠ 0 := by
    rw [p4Q2LB_originalPhysicalUnitPosteriorTestGap_factorization
      H b hb.le left₀ right e h u₀ u]
    exact mul_ne_zero hC.ne' hu
  have hQ :
      p4Q2JQ_originalPhysicalGIDensityWeight H b hb.le
        (Function.update left₀ e u, right) ≠ 0 :=
    (p4Q2JQ_originalPhysicalGIDensityWeight_pos H b hb.le
      (Function.update left₀ e u, right)).ne'
  rw [p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div]
  exact div_ne_zero (neg_ne_zero.mpr hTest) hQ

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LB_originalPhysicalUnitSignedCompensatedRightSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LB_originalPhysicalUnitPosteriorTestGap_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LB_originalPhysicalUnitGI_nonzero_some_actualLeftBoundary
