import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullSpatialExponentialHaarStrictPosV5_LI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonPhysicalSourceGIBridgeV5_JU
import Mathlib.Tactic

/-!
# P4-Q2-LJ — TRUE complete spatial Wilson one-slab kernel strict positivity

LI proved strict spatial Haar quadratic positivity for the actual
full-link SU(2) temporal crossing Wilson kernel, for every nonzero
continuous signed source and positive finite-volume Wilson beta.

The ACTUAL original complete one-slab kernel is NOT merely the
crossing product: it includes the strictly positive spatial Wilson
half-Boltzmann amplitudes on BOTH real boundary configurations.
Here we retain those actual halfweights exactly and prove that
multiplying an arbitrary nonzero continuous signed spatial source
by the positive original halfweight cannot annihilate it.

This gives strict positive full-spatial Haar quadratic energy of the
LITERAL original complete one-slab kernel. Using its original
symmetry and the strict quadratic energy, we then prove existence
of some genuine right spatial configuration B where the ORIGINAL
Wilson transfer integral of EVERY nonzero continuous spatial
source ψ is nonzero. No artificial rank, detector frame, or
invented transfer is assumed.

The original continuous source is finally connected to an ACTUAL
Gauss-law physical L² source by its genuine Haar-a.e.
representative, and specialized to JU's ORIGINAL centered spatial
Wilson action physical source (which JK already proves nonzero
in Haar L²). Thus this concrete physical centered source has a
genuinely nonzero original Wilson transfer at SOME right boundary.

The stronger LC right-link-identity witness, two-context GI minor,
H1-C3/continuum limits and volume-uniform gap remain separate.
No independent Haar posterior replacement, sorry/admit/new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "haarPair" => Measure.prod haar haar
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2

/-- The continuous TRUE spatial Wilson halfweight on the actual
finite-volume original spatial SU(2) configurations. -/
noncomputable def p4Q2LJ_originalSpatialWilsonHalfWeightContinuous
    (b : ℝ) : C(Cfg, ℝ) :=
  ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 b,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 b⟩

@[simp] theorem p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_apply
    (b : ℝ) (A : Cfg) :
    p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b A =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 b A :=
  rfl

theorem p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_pos
    (b : ℝ) (A : Cfg) :
    0 < p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b A :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos H 2 b A

/-- Multiplying a true signed continuous spatial source by the
ACTUAL strictly positive Boltzmann halfweight. -/
noncomputable def p4Q2LJ_originalSpatialWilsonHalfWeightedSource
    (b : ℝ) (ψ : C(Cfg, ℝ)) : C(Cfg, ℝ) :=
  ψ * p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b

@[simp] theorem p4Q2LJ_originalSpatialWilsonHalfWeightedSource_apply
    (b : ℝ) (ψ : C(Cfg, ℝ)) (A : Cfg) :
    p4Q2LJ_originalSpatialWilsonHalfWeightedSource H b ψ A =
      ψ A * p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b A :=
  rfl

/-- The strictly positive ACTUAL Wilson halfweight never erases
a nonzero continuous source, for arbitrary b and finite H. -/
theorem p4Q2LJ_originalSpatialWilsonHalfWeightedSource_ne_zero
    (b : ℝ) (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0) :
    p4Q2LJ_originalSpatialWilsonHalfWeightedSource H b ψ ≠ 0 := by
  intro hz
  apply hψ
  ext A
  have hAt := congrArg (fun f : C(Cfg, ℝ) => f A) hz
  have hMul : ψ A *
      p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b A = 0 := by
    simpa only [p4Q2LJ_originalSpatialWilsonHalfWeightedSource_apply,
      ContinuousMap.zero_apply] using hAt
  have hZero : ψ A = 0 :=
    (mul_eq_zero.mp hMul).resolve_right
      (p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_pos H b A).ne'
  simpa using hZero

/-- Genuine original, jointly continuous complete Wilson one-slab
kernel, including BOTH physical half-Boltzmann boundary factors. -/
noncomputable def p4Q2LJ_originalFullWilsonOneSlabContinuous
    (b : ℝ) : C(Cfg × Cfg, ℝ) :=
  ⟨(fun p => K b p.1 p.2),
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 b⟩

@[simp] theorem p4Q2LJ_originalFullWilsonOneSlabContinuous_apply
    (b : ℝ) (A B : Cfg) :
    p4Q2LJ_originalFullWilsonOneSlabContinuous H b (A,B) =
      K b A B := rfl

/-- The original FULL one-slab Wilson kernel equals the original
temporal CROSSING Wilson kernel sandwiched by exact positive
spatial Boltzmann halfweights, at actual spatial boundaries. -/
theorem p4Q2LJ_originalFullWilsonOneSlab_eq_originalWeightedCrossing
    (b : ℝ) (A B : Cfg) :
    p4Q2LJ_originalFullWilsonOneSlabContinuous H b (A,B) =
      p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b A *
        p4Q2LI_originalSpatialWilsonCrossingContinuous H b (A,B) *
          p4Q2LJ_originalSpatialWilsonHalfWeightContinuous H b B := by
  rw [p4Q2LJ_originalFullWilsonOneSlabContinuous_apply,
    p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_apply,
    p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_apply,
    p4Q2LI_originalSpatialWilsonCrossingContinuous_apply]
  rfl

/-- Exact full-spatial Haar quadratic form identity:
the original COMPLETE Wilson slab evaluated on ψ equals
the original CROSSING Wilson quadratic evaluated on the ACTUAL
halfweight-multiplied source. -/
theorem p4Q2LJ_originalFullSlabHaarQuadratic_eq_weightedCrossing
    (b : ℝ) (ψ : C(Cfg, ℝ)) :
    p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
      (p4Q2LJ_originalFullWilsonOneSlabContinuous H b) =
    p4Q2LI_originalFullSpatialPairHaarMomentCLM H
      (p4Q2LJ_originalSpatialWilsonHalfWeightedSource H b ψ)
      (p4Q2LI_originalSpatialWilsonCrossingContinuous H b) := by
  rw [p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply,
    p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply]
  apply integral_congr_ae
  filter_upwards with p
  rcases p with ⟨A, B⟩
  rw [p4Q2LJ_originalFullWilsonOneSlab_eq_originalWeightedCrossing]
  simp only [p4Q2LJ_originalSpatialWilsonHalfWeightedSource_apply]
  ring

/-- The ACTUAL original complete finite-volume SU(2) Wilson
one-slab kernel is strictly positive on every nonzero continuous
signed spatial source, not just PSD and not merely the crossing. -/
theorem p4Q2LJ_originalFullWilsonOneSlabHaarQuadratic_pos
    (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    0 < p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
      (p4Q2LJ_originalFullWilsonOneSlabContinuous H b) := by
  rw [p4Q2LJ_originalFullSlabHaarQuadratic_eq_weightedCrossing]
  exact p4Q2LI_originalSpatialWilsonCrossingHaarQuadratic_pos H
    (p4Q2LJ_originalSpatialWilsonHalfWeightedSource H b ψ)
    (p4Q2LJ_originalSpatialWilsonHalfWeightedSource_ne_zero H b ψ hψ)
    b hb

/-- Literal original complete one-slab Wilson kernel has STRICTLY
positive REAL spatial Haar double quadratic integral against any
nonzero signed continuous spatial source at positive Wilson beta. -/
theorem p4Q2LJ_originalFullWilsonOneSlabHaarDoubleIntegral_pos
    (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    0 < (∫ A : Cfg, ∫ B : Cfg,
      K b A B * (ψ A * ψ B) ∂haar ∂haar) := by
  let F : C(Cfg × Cfg, ℝ) := p4Q2LJ_originalFullWilsonOneSlabContinuous H b
  have hCont : Continuous (fun p : Cfg × Cfg =>
      F p * (ψ p.1 * ψ p.2)) :=
    F.continuous.mul
      ((ψ.continuous.comp continuous_fst).mul
        (ψ.continuous.comp continuous_snd))
  have hInt : Integrable (fun p : Cfg × Cfg =>
      F p * (ψ p.1 * ψ p.2)) haarPair :=
    hCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPos :=
    p4Q2LJ_originalFullWilsonOneSlabHaarQuadratic_pos H ψ hψ b hb
  rw [p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply] at hPos
  rw [integral_prod _ hInt] at hPos
  change
    0 < (∫ A : Cfg, ∫ B : Cfg,
      p4Q2LJ_originalFullWilsonOneSlabContinuous H b (A,B) *
        (ψ A * ψ B) ∂haar ∂haar) at hPos
  simpa only [p4Q2LJ_originalFullWilsonOneSlabContinuous_apply] using hPos

/-- TRUE original all-spatial-link Wilson kernel sends EVERY
nonzero continuous signed spatial source to some nonzero right
boundary value. This follows from the ACTUAL strictly positive
complete one-slab quadratic plus its original symmetry, not from
any artificial injectivity/rank premise. -/
theorem p4Q2LJ_originalFullWilsonKernelTransfer_exists_nonzero
    (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    ∃ B : Cfg,
      (∫ A : Cfg, K b A B * ψ A ∂haar) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hSym (A B : Cfg) :
      K b A B = K b B A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
      H 2 (by norm_num) b hb.le A B
  have hInnerZero (A : Cfg) :
      (∫ B : Cfg, K b A B * (ψ A * ψ B) ∂haar) = 0 := by
    calc
      (∫ B : Cfg, K b A B * (ψ A * ψ B) ∂haar) =
        ψ A * (∫ B : Cfg, K b B A * ψ B ∂haar) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with B
          rw [hSym A B]
          ring
      _ = 0 := by rw [hn A]; ring
  have hQuadraticZero :
      (∫ A : Cfg, ∫ B : Cfg,
        K b A B * (ψ A * ψ B) ∂haar ∂haar) = 0 := by
    simp_rw [hInnerZero]
    simp
  exact (ne_of_gt
    (p4Q2LJ_originalFullWilsonOneSlabHaarDoubleIntegral_pos
      H ψ hψ b hb)) hQuadraticZero

/-- The actual Gauss-law physical Haar-L² one-slab transfer
integral is exactly the original Wilson kernel integral against
its authentic continuous Haar-a.e. representative. -/
theorem p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
    (b : ℝ) (f : Phys) (ψ : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => (f : Lp ℝ 2 haar) A) =ᵐ[haar] ψ)
    (B : Cfg) :
    decomposableOneSliceTransferIntegral H 2 b f B =
      ∫ A : Cfg, K b A B * ψ A ∂haar := by
  unfold decomposableOneSliceTransferIntegral
  apply integral_congr_ae
  filter_upwards [hRep] with A hA
  rw [hA]

/-- Any NONZERO genuine physical Gauss-law L² source with an
ACTUAL nonzero continuous spatial representative has a nonzero
original finite-volume Wilson transfer at SOME right boundary. -/
theorem p4Q2LJ_originalPhysicalTransfer_exists_nonzero_of_continuousRepresentative
    (b : ℝ) (hb : 0 < b) (f : Phys) (ψ : C(Cfg, ℝ))
    (hLp : (f : Lp ℝ 2 haar) = ContinuousMap.toLp 2 haar ℝ ψ)
    (hψ : ψ ≠ 0) :
    ∃ B : Cfg,
      decomposableOneSliceTransferIntegral H 2 b f B ≠ 0 := by
  have hRep :
      (fun A : Cfg => (f : Lp ℝ 2 haar) A) =ᵐ[haar] ψ := by
    rw [hLp]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  obtain ⟨B, hB⟩ :=
    p4Q2LJ_originalFullWilsonKernelTransfer_exists_nonzero H ψ hψ b hb
  refine ⟨B, ?_⟩
  rw [p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
    H b f ψ hRep B]
  exact hB

/-- The ORIGINAL anchored and centered spatial Wilson action
is an ACTUAL physical Gauss-law Hilbert source (JU), with a
NONZERO original Wilson full-spatial transfer at some right
boundary, for every positive beta. This is the genuine centered
source, not an auxiliary Wilson test. The LC fixed-identity
right-fiber criterion is NOT asserted here. -/
theorem p4Q2LJ_originalCenteredSpatialWilsonPhysicalTransfer_exists_nonzero
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Cfg × Cfg) :
    ∃ B : Cfg,
      decomposableOneSliceTransferIntegral H 2 b
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
          H b hb.le e z) B ≠ 0 := by
  let ψ : C(Cfg, ℝ) := p4Q2JK_anchorCenteredSpatialWilson H b hb.le e z
  have hψLp : ContinuousMap.toLp 2 haar ℝ ψ ≠ 0 :=
    p4Q2JK_anchorCenteredSpatialWilson_HaarLp_ne_zero H b hb.le e z
  have hψ : ψ ≠ 0 := by
    intro hz
    apply hψLp
    rw [hz]
    map_zero
  have hLp :
      ((p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
          H b hb.le e z : Phys) : Lp ℝ 2 haar) =
        ContinuousMap.toLp 2 haar ℝ ψ :=
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp
      H b hb.le e z
  exact p4Q2LJ_originalPhysicalTransfer_exists_nonzero_of_continuousRepresentative
    H b hb
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb.le e z)
    ψ hLp hψ

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalSpatialWilsonHalfWeightContinuous_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalSpatialWilsonHalfWeightedSource_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalSpatialWilsonHalfWeightedSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalFullWilsonOneSlabContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalFullWilsonOneSlab_eq_originalWeightedCrossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalFullSlabHaarQuadratic_eq_weightedCrossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalFullWilsonOneSlabHaarQuadratic_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalFullWilsonOneSlabHaarDoubleIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalFullWilsonKernelTransfer_exists_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalPhysicalTransfer_exists_nonzero_of_continuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LJ_originalCenteredSpatialWilsonPhysicalTransfer_exists_nonzero
