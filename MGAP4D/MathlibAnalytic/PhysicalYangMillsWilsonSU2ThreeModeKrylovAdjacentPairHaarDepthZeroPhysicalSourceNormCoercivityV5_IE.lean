import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIOpenPhysicalSourceDetectionV5_ID
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFiniteGLSOSComplementComparisonV5_HR
import Mathlib.Tactic

/-!
# P4-Q2-IE: true physical-source-norm comparison of original Wilson GL mass

The original physical Haar-L² source Gram Qsrc is distinct from the
original GL two-interacting-Wilson-posterior integral detector Gram B.
First the exact mathlib Matrix.gram identity is specialized to the
ACTUAL gauge-invariant physical Krylov source family:
  aᵀ Qsrc a = ‖S(a)‖_(genuine physical Haar L²)^2,
for every finite depth and any nonnegative fine coupling.

At depth r=0, IB proves K=ker S=bot for every fine beta(n+1)>=0
when frozen beta(n)>0, and the TRUE original spatial GL mass is
strictly positive for each nonzero actual signed zero-mode coefficient.
The real physical source Gram Qsrc is also positive definite there,
because its Rayleigh equals the genuine physical source squared norm.

Apply HR's pinned-mathlib compact-unit-sphere finite-dimensional
quadratic comparison to the TWO independently constructed original
Wilson and physical source Gram forms, not to a synthetic frame.
The result is an ACTUAL fixed-model quantitative source-norm
coercivity and upper bound:
  exists 0<c<=C such that for EVERY a,
      c*‖S(a)‖² <= M_GL(S(a)) <= C*‖S(a)‖².

The constants are existential, may depend on finite physical volume,
frozen beta, fine beta, scale, and choice of geometry, and are NOT
explicit or uniform as lattice spacing/volume vary. This is restricted
to the one-mode physical source family r=0; it does NOT prove arbitrary
positive-fine higher-depth injectivity, H1-C3, OS, or continuum 4D gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2IE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IE_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ArbitraryActualDepth

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- The actual ORIGINAL source Haar-L² Gram (NOT the pair-Haar
residual or the detector Gram) is exactly the squared norm of
the genuine signed gauge-invariant physical source synthesis.
This equality is valid even with linearly dependent Krylov modes,
zero fine beta, and arbitrary depth. -/
theorem p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
    (a : Coeff) :
    star a ⬝ᵥ ((Qsrc) *ᵥ a) =
      ‖∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)‖ ^ 2 := by
  let v : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        Hn 2 := fun j => RightFactor n (j : ℕ)
  change star a ⬝ᵥ ((Matrix.gram ℝ v) *ᵥ a) =
    ‖∑ j : Fin (r + 1), a j • v j‖ ^ 2
  calc
    star a ⬝ᵥ ((Matrix.gram ℝ v) *ᵥ a) =
        ⟪∑ j : Fin (r + 1), a j • v j,
          ∑ j : Fin (r + 1), a j • v j⟫_ℝ :=
      Matrix.star_dotProduct_gram_mulVec v a a
    _ = ‖∑ j : Fin (r + 1), a j • v j‖ ^ 2 := by
      exact inner_self_eq_norm_sq_to_K _

end ArbitraryActualDepth

section ZeroDepth

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (0 + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0

/-- For EVERY nonnegative fine beta(n+1), the two genuinely distinct
physical quadratic forms B and Qsrc are each positive definite on
the actual depth-zero real signed coefficient space. No frame axiom. -/
theorem p4Q2IE_depthZero_bothOriginalWilson_and_sourceGram_positive
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link)
    (a : Coeff) (ha : a ≠ 0) :
    (0 < star a ⬝ᵥ ((B hFrozen) *ᵥ a)) ∧
    (0 < star a ⬝ᵥ ((Qsrc) *ᵥ a)) := by
  have hB : 0 < star a ⬝ᵥ ((B hFrozen) *ᵥ a) := by
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 hFrozen a]
    exact p4Q2IB_depthZero_originalWilsonGLMass_pos_of_coeff_ne_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e a ha
  have hSourceKer : (PhysicalSource).ker = ⊥ :=
    (p4Q2IB_depthZero_originalGI_jointKernel_eq_physicalSourceKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e).symm.trans
      (p4Q2IB_depthZero_originalGI_jointKernel_eq_bot
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n hFrozen right e)
  have hSource : PhysicalSource a ≠ 0 := by
    intro hs
    have hMem : a ∈ (PhysicalSource).ker :=
      (LinearMap.mem_ker).mpr hs
    rw [hSourceKer] at hMem
    exact ha (by simpa using hMem)
  have hQ : 0 < star a ⬝ᵥ ((Qsrc) *ᵥ a) := by
    rw [p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 a]
    change 0 < ‖PhysicalSource a‖ ^ 2
    exact pow_pos (norm_pos_iff.mpr hSource) 2
  exact ⟨hB, hQ⟩

/-- Genuine fixed-volume physical-Haar-L²-SOURCE-NORM coercivity:
original two-Wilson-posterior pair-Haar GL spatial integral mass is
bounded above and below by the squared norm of the ORIGINAL physical
signed fine-right depth-zero source, for any nonnegative fine beta.
These strictly positive constants need not be numerically known or
uniform in physical volume, scale, frozen/fine coupling, etc. -/
theorem p4Q2IE_depthZero_originalWilsonGLMass_physicalSourceNorm_fixed_comparison
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * ‖∑ j : Fin (0 + 1), a j • RightFactor n (j : ℕ)‖ ^ 2 ≤
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (0 + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (0 + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ≤
          C * ‖∑ j : Fin (0 + 1), a j • RightFactor n (j : ℕ)‖ ^ 2 := by
  have hPosB (a : Coeff) (ha : a ≠ 0) :
      0 < star a ⬝ᵥ ((B hFrozen) *ᵥ a) :=
    (p4Q2IE_depthZero_bothOriginalWilson_and_sourceGram_positive
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e a ha).1
  have hPosQ (a : Coeff) (ha : a ≠ 0) :
      0 < star a ⬝ᵥ ((Qsrc) *ᵥ a) :=
    (p4Q2IE_depthZero_bothOriginalWilson_and_sourceGram_positive
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e a ha).2
  obtain ⟨c, C, hc, hcC, hComp⟩ :=
    p4Q2HR_finiteDimensional_positive_quadratics_comparable
      (fun a : Coeff => star a ⬝ᵥ ((B hFrozen) *ᵥ a))
      (fun a : Coeff => star a ⬝ᵥ ((Qsrc) *ᵥ a))
      (p4Q2HR_realMatrix_quad_continuous (B hFrozen))
      (p4Q2HR_realMatrix_quad_continuous Qsrc)
      (fun c a => p4Q2HR_realMatrix_quad_smul (B hFrozen) c a)
      (fun c a => p4Q2HR_realMatrix_quad_smul Qsrc c a)
      hPosB hPosQ
  refine ⟨c, C, hc, hcC, ?_⟩
  intro a
  have hBquad :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 hFrozen a
  have hQquad :=
    p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 a
  simpa only [hBquad, hQquad] using hComp a

end ZeroDepth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IE_depthZero_bothOriginalWilson_and_sourceGram_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IE_depthZero_originalWilsonGLMass_physicalSourceNorm_fixed_comparison
