import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIFiniteModeContinuityDetectionV5_HH
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSingleLinkFellerClosure
import Mathlib.Tactic

/-!
# P4-Q2-HI: genuine two-Wilson-posterior GI expectation gaps are jointly continuous

GN expresses the original signed physical two-posterior expectation gap as a
genuine SU(2) Haar pairing. FF has already constructed the original physical
signed receiver as a bounded continuous function, for every physical Haar-L²
source. The original Wilson posterior fiber log weights (not independent Haar
posterior substitutes) are jointly continuous in the right environment and the
inserted SU(2) value by the existing physical Feller closure.

This file joins those previously proven results with the compact-domain
parametric-integral theorem and the strictly positive ORIGINAL Wilson
partition functions, giving unconditional boundary-pair continuity of the
original GI expectation gap for every physical source at beta >= 0.

Consequently HH's finite mode-continuity assumptions can be discharged
without a source frame or mode independence: at frozen beta > 0, true GL
gap-square detection mass vanishes exactly on the original all-boundary GI
joint kernel for arbitrary nonnegative fine coupling.

No GI detector injectivity, equality of the joint kernel with the physical
source synthesis kernel, volume-uniform frame, H1-C3, or continuum Yang-Mills
mass gap follows from continuity.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1100000

local instance p4Q2HI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HI_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A continuous family of the ORIGINAL normalized exponential densities is
jointly continuous in its parameter and gauge coordinate. The normalization
is an actual positive compact-Haar integral, not an assumed denominator. -/
theorem p4Q2HI_normalizedExp_joint_continuous
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (ℓ : P → X → ℝ)
    (hℓ : Continuous (Function.uncurry ℓ)) :
    Continuous (fun q : P × X => continuousNormalizedExp μ (ℓ q.1) q.2) := by
  have hSlice (p : P) : Continuous (ℓ p) := by
    simpa only [Function.uncurry] using
      (hℓ.comp (continuous_const.prodMk continuous_id :
        Continuous (fun x : X => (p, x))))
  have hZ : Continuous (fun p : P => continuousExpPartition μ (ℓ p)) := by
    change Continuous (fun p : P => ∫ x, Real.exp (ℓ p x) ∂μ)
    exact continuous_integral_compact_domain μ
      (fun p x => Real.exp (ℓ p x)) (Real.continuous_exp.comp hℓ)
  have hNum : Continuous (fun q : P × X => Real.exp (ℓ q.1 q.2)) :=
    Real.continuous_exp.comp hℓ
  have hDenom : Continuous (fun q : P × X => continuousExpPartition μ (ℓ q.1)) :=
    hZ.comp continuous_fst
  change Continuous (fun q : P × X =>
    Real.exp (ℓ q.1 q.2) / continuousExpPartition μ (ℓ q.1))
  exact hNum.div hDenom (fun q =>
    (continuousExpPartition_pos μ (ℓ q.1) (hSlice q.1)).ne')

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H

/-- The difference of the TWO ACTUAL normalized Wilson posterior densities
is jointly continuous in the entire physical right environment and the
inserted SU(2) variable. Previous GN continuity fixed the environment;
the Feller log-weight theorem supplies the missing joint parameter. -/
theorem p4Q2HI_originalWilsonPosteriorDensityContrast_joint_continuous
    (e : Link) :
    Continuous (fun q : Cfg × Gauge =>
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H beta hbeta q.1 e q.2) := by
  let μ : Measure Gauge := normalizedCompactHaar Gauge
  let ℓ₀ : Cfg → Gauge → ℝ := fun B g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) B e g
  let ℓ₁ : Cfg → Gauge → ℝ := fun B g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) B e g
  have hℓ₀ : Continuous (Function.uncurry ℓ₀) := by
    simpa only [ℓ₀, Function.uncurry] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_prod_continuous
        H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) e)
  have hℓ₁ : Continuous (Function.uncurry ℓ₁) := by
    simpa only [ℓ₁, Function.uncurry] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_prod_continuous
        H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) e)
  have h₀ : Continuous (fun q : Cfg × Gauge =>
      continuousNormalizedExp μ (ℓ₀ q.1) q.2) :=
    p4Q2HI_normalizedExp_joint_continuous μ ℓ₀ hℓ₀
  have h₁ : Continuous (fun q : Cfg × Gauge =>
      continuousNormalizedExp μ (ℓ₁ q.1) q.2) :=
    p4Q2HI_normalizedExp_joint_continuous μ ℓ₁ hℓ₁
  change Continuous (fun q : Cfg × Gauge =>
    continuousNormalizedExp μ (ℓ₀ q.1) q.2 -
    continuousNormalizedExp μ (ℓ₁ q.1) q.2)
  exact h₀.sub h₁

/-- The exact original Wilson Haar pairing is continuous in the complete
physical boundary pair. This is proved separately from the GI-definitional
conversion to keep Lean WHNF normalization small on genuine physical types. -/
theorem p4Q2HI_originalWilsonGI_HaarPairing_continuous
    (f : Phys) (e : Link) :
    Continuous (fun z : Cfg × Cfg =>
      ∫ g : Gauge,
        p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
          H 2 (by norm_num) beta hbeta f e (z,g) *
        p4Q2GB_originalWilsonPosteriorLeftDensityContrast
          H beta hbeta z.2 e g
        ∂normalizedCompactHaar Gauge) := by
  let μ : Measure Gauge := normalizedCompactHaar Gauge
  let R := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta hbeta f e
  let D : Cfg → Gauge → ℝ := fun B g =>
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H beta hbeta B e g
  have hD : Continuous (Function.uncurry D) := by
    simpa only [D, Function.uncurry] using
      (p4Q2HI_originalWilsonPosteriorDensityContrast_joint_continuous
        H beta hbeta e)
  have hEnv : Continuous (fun q : (Cfg × Cfg) × Gauge => (q.1.2, q.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have hIntg : Continuous (fun q : (Cfg × Cfg) × Gauge =>
      R q * D q.1.2 q.2) :=
    R.continuous.mul (hD.comp hEnv)
  have hIntegral : Continuous (fun z : Cfg × Cfg =>
      ∫ g : Gauge, R (z,g) * D z.2 g ∂μ) :=
    continuous_integral_compact_domain μ
      (fun z g => R (z,g) * D z.2 g) hIntg
  exact hIntegral

/-- Every genuine original physical Haar-L² source has a continuous
two-interacting-Wilson-posterior GI expectation gap on the FULL pair of
spatial boundary configurations, for all frozen beta >= 0. The original
FF signed receiver and both actual Wilson density rows remain intact. -/
theorem p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
    (f : Phys) (e : Link) :
    Continuous (fun z : Cfg × Cfg =>
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta f e z) := by
  have hPairing :=
    p4Q2HI_originalWilsonGI_HaarPairing_continuous H beta hbeta f e
  have hEq :
      (fun z : Cfg × Cfg =>
        ∫ g : Gauge,
          p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
            H 2 (by norm_num) beta hbeta f e (z,g) *
          p4Q2GB_originalWilsonPosteriorLeftDensityContrast
            H beta hbeta z.2 e g
          ∂normalizedCompactHaar Gauge) =
      (fun z : Cfg × Cfg =>
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta hbeta f e z) := by
    funext z
    exact (p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing
      H beta hbeta f e z).symm
  exact hEq ▸ hPairing

end Frozen

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- HI removes the r+1 genuine GI mode-continuity hypotheses of HH
unconditionally, with NO assumption on fine coupling except nonnegativity. -/
theorem p4Q2HI_actualRightGI_finiteModes_continuous
    (e : Link) (j : Fin (r + 1)) :
    Continuous (fun z : Cfg × Cfg =>
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (RightFactor n (j : ℕ)) e z) :=
  p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
    Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e

/-- Unconditional exact identification of genuine GL detection-null source
combinations with the ALL-boundary GI common real kernel at frozen beta>0.
There is no physical source injectivity hypothesis here. -/
theorem p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) = 0 ↔
      a ∈ p4Q2HG_actualRightGIJointModalKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r := by
  exact p4Q2HH_actualRightGLMass_zero_iff_GI_jointKernel_of_modeContinuity
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen
    (fun e j => p4Q2HI_actualRightGI_finiteModes_continuous
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j) a

/-- A coefficient outside the true all-boundary GI common kernel has
strictly positive ORIGINAL GL two-posterior gap-square detection mass. -/
theorem p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (hNot : a ∉ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) := by
  exact p4Q2HH_actualRightGLMass_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen
    (fun e j => p4Q2HI_actualRightGI_finiteModes_continuous
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j) a hNot

/-- Genuine physical right-Krylov Gram positivity follows on the
complement of the GI common kernel, not on all nonzero coefficient
vectors. Coefficient independence and continuum uniformity stay OPEN. -/
theorem p4Q2HI_actualRightGram_pos_of_not_mem_jointKernel
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (hNot : a ∉ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) := by
  exact p4Q2HH_actualRightGram_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen
    (fun e j => p4Q2HI_actualRightGI_finiteModes_continuous
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j) a hNot

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_normalizedExp_joint_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_originalWilsonPosteriorDensityContrast_joint_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_originalWilsonGI_HaarPairing_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_actualRightGI_finiteModes_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HI_actualRightGram_pos_of_not_mem_jointKernel
