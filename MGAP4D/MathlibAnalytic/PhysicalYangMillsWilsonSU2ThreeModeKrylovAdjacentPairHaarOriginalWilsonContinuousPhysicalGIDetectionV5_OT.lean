import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFinePhysicalNormCoercivityV5_OS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullOneSlabStrictTransferV5_LJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaugeNormalizedCenteredTransferV5_LK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSourceLeftLinkFactorizationV5_LC
import Mathlib.Tactic

/-!
# P4-Q2-OT — true Wilson continuous physical source detection by original GI receiver

This is an ANALYTIC bridge between the unchanged, positive-coupling
original SU(2) Wilson kernel and the unchanged two-interacting-posterior
signed GI detector; it does not postulate an arbitrary source rank.

LJ proves strict positivity of the FULL (spatial halfweights included)
original Wilson one-slab double Haar integral for every nonzero
continuous signed source. LK proves covariance of the SAME physical
Wilson transfer of a source possessing a gauge-invariant continuous
Haar-L² representative. It also constructs the actual lattice gauge
transformation putting any selected right link at SU(2) identity.
LC proves that a nonzero original Wilson transfer at this identity
right-link fiber is genuinely detected by some actual left SU(2)
boundary through the ORIGINAL two interacting Wilson posteriors.

Combining these established independent analytic results proves:
every nonzero genuine Gauss-law physical Hilbert source with an
ACTUAL gauge-invariant continuous Haar-L² representative has nonzero
original interacting-two-posterior signed GI response in a REAL
link/boundary context, at every positive frozen coupling.

For the EXACT depth-two OO Schur physical source, this eliminates the
third-detector obstruction IF that same true source is nonzero AND
its required continuous invariant representative is constructed.
Neither regularity nor physical source nonzero is assumed to follow
automatically from coefficient nonzero. These remain separate
obligations for the actual normalized fine Wilson Krylov orbit.

All original frozen/fine couplings, actual original Wilson transfer,
Gauss-law carrier, Perron factors and interacting posteriors remain
unchanged. No Dobrushin, independent-Haar posterior, sorry/admit,
new axiom, volume-uniform U0 or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section FrozenTrueWilsonContinuousSource
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GT" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "GaugeAct" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2

/-- Actual continuous representative in full physical product Haar-L²,
with the EXACT original lattice gauge action. This is a regularity
property on a genuine physical source, not an arbitrary detector rank
or an independently modified Wilson model. -/
def p4Q2OT_hasGaugeContinuousRepresentative (f : Phys) : Prop :=
  ∃ ψ : C(Cfg, ℝ),
    (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] ψ ∧
      ∀ gamma : GT, ∀ A : Cfg, ψ (GaugeAct gamma A) = ψ A

/-- If the genuine physical Haar-L² source is nonzero, none of its
pointwise continuous representatives can be identically zero. -/
theorem p4Q2OT_originalContinuousRepresentative_ne_zero
    (f : Phys) (hf : f ≠ 0) (ψ : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] ψ) :
    ψ ≠ 0 := by
  have hLp : ((f : Phys) : Lp ℝ 2 haar) =
      ContinuousMap.toLp 2 haar ℝ ψ := by
    apply Lp.ext
    exact hRep.trans (ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar).symm
  intro hZero
  apply hf
  apply Subtype.ext
  rw [hLp, hZero]
  simp

/-- Authentic Wilson spectral positivity + actual spatial gauge
normalization give a NONZERO transfer of the SAME physical source
on a right-link identity fiber, for ANY chosen genuine spatial link.
No fictitious test source is introduced. -/
theorem p4Q2OT_originalContinuousPhysical_transfer_nonzero_identityFiber
    (b : ℝ) (hb : 0 < b) (f : Phys)
    (ψ : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] ψ)
    (hψ : ψ ≠ 0)
    (hGauge : ∀ gamma : GT, ∀ A : Cfg,
      ψ (GaugeAct gamma A) = ψ A)
    (e : Link) :
    ∃ R : Cfg,
      decomposableOneSliceTransferIntegral H 2 b f
        (Function.update R e (1 : Gauge)) ≠ 0 := by
  obtain ⟨B, hB⟩ :=
    p4Q2LJ_originalFullWilsonKernelTransfer_exists_nonzero H ψ hψ b hb
  have hBPhysical :
      decomposableOneSliceTransferIntegral H 2 b f B ≠ 0 := by
    rw [p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
      H b f ψ hRep B]
    exact hB
  let gamma : GT :=
    p4Q2LK_originalSpatialRightLinkGaugeNormalizer H B e
  let R : Cfg := GaugeAct gamma B
  have hIdentity : R e = (1 : Gauge) :=
    p4Q2LK_originalSpatialRightLinkGaugeNormalizer_apply H B e
  have hUpdate : Function.update R e (1 : Gauge) = R := by
    funext k
    by_cases hk : k = e
    · subst k
      simp [hIdentity]
    · simp [Function.update, hk]
  have hCov :
      decomposableOneSliceTransferIntegral H 2 b f R =
        decomposableOneSliceTransferIntegral H 2 b f B :=
    p4Q2LK_originalPhysicalTransfer_gaugeInvariant_of_continuousRepresentative
      H b f ψ hRep hGauge gamma B
  refine ⟨R, ?_⟩
  rw [hUpdate, hCov]
  exact hBPhysical

/-- This genuinely positive original Wilson physical source is
detectable by an ACTUAL original two-interacting-posterior GI receiver,
via LJ strict positivity, LK gauge-normalized fiber and LC's original
Perron + signed exponential-Haar factorization. The GI link may be
selected before the two-posterior boundary context. -/
theorem p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
    (b : ℝ) (hb : 0 < b) (f : Phys) (hf : f ≠ 0)
    (hRegular : p4Q2OT_hasGaugeContinuousRepresentative H f)
    (e : Link) (left₀ : Cfg) :
    ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e z ≠ 0 := by
  obtain ⟨ψ, hRep, hGauge⟩ := hRegular
  have hψ : ψ ≠ 0 :=
    p4Q2OT_originalContinuousRepresentative_ne_zero
      H f hf ψ hRep
  obtain ⟨R, hR⟩ :=
    p4Q2OT_originalContinuousPhysical_transfer_nonzero_identityFiber
      H b hb f ψ hRep hψ hGauge e
  obtain ⟨u, hu⟩ :=
    p4Q2LC_originalPhysicalGI_nonzero_some_left_of_transfer_identity
      H b hb f left₀ R e (1 : Gauge) (1 : Gauge) hR
  exact ⟨(Function.update left₀ e u, R), hu⟩

end FrozenTrueWilsonContinuousSource

section ActualKrylovSchurThirdGIDetection
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- The EXACT same authentic OO physical Schur source, once proved
nonzero and provided with its true continuous Gauss-law representative,
is necessarily detected by a THIRD genuine two-posterior Wilson
GI link/boundary context. This is *not* a hypothetical receiver rank.

The remaining regularity obligation is on the actual repeated
normalized fine Wilson operator; it is NOT asserted here. -/
theorem p4Q2OT_originalSchurPhysical_nonzero_regular_implies_thirdTrueGI
    (hFrozen : 0 < beta n)
    (e e' : Link) (z z' : Pair)
    (hSchur :
      S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0)
    (hRegular :
      p4Q2OT_hasGaugeContinuousRepresentative Hn
        (S 2 (p4Q2OO_depthTwoSchurResidual
          (M 2 e z) (M 2 e' z')))) :
    ∃ e'' : Link, ∃ z'' : Pair,
      M 2 e'' z''
        (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0 := by
  let f : Phys :=
    S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z'))
  obtain ⟨z'', hGI⟩ :=
    p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
      Hn (beta n) hFrozen f hSchur hRegular e z.1
  refine ⟨e, z'', ?_⟩
  rw [p4Q2OO_actualDepthTwo_SchurResidual_trueThirdGI_response
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e e' e z z' z'']
  exact hGI

/-- Thus nonzero true Schur source plus genuine continuous-physical
regularity forces both the actual all-context signed GI detector and
the original Gauss-law three-mode physical synthesis to be injective.
The original OM first-two minor is still explicitly required. -/
theorem p4Q2OT_originalSchurPhysical_regular_nonzero_bothInjective
    (hFrozen : 0 < beta n)
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor
      (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur :
      S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0)
    (hRegular :
      p4Q2OT_hasGaugeContinuousRepresentative Hn
        (S 2 (p4Q2OO_depthTwoSchurResidual
          (M 2 e z) (M 2 e' z')))) :
    Function.Injective
      (p4Q2HJ_actualRightGIContinuousDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2) ∧
    Function.Injective (S 2) := by
  obtain ⟨e'', z'', hThird⟩ :=
    p4Q2OT_originalSchurPhysical_nonzero_regular_implies_thirdTrueGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' z z' hSchur hRegular
  exact p4Q2OP_actualDepthTwo_actualThirdGI_nonzero_implies_bothInjective
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e e' e'' z z' z'' hMinor hThird

end ActualKrylovSchurThirdGIDetection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OT_originalContinuousRepresentative_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OT_originalContinuousPhysical_transfer_nonzero_identityFiber
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OT_originalSchurPhysical_nonzero_regular_implies_thirdTrueGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OT_originalSchurPhysical_regular_nonzero_bothInjective
