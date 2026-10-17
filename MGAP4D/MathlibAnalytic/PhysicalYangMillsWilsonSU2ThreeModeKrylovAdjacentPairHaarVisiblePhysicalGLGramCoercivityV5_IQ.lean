import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVisiblePhysicalGIStabilityV5_IP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGLPhysicalSourceNormOnGIComplementV5_IG
import Mathlib.Tactic

/-!
# P4-Q2-IQ: original Wilson GL Gram versus actual visible physical Haar-L² source norm

This is a FIXED FINITE MODEL result for the ACTUAL original Wilson
SU(2) two-interacting-posterior spatial GL mass and the TRUE signed
fine-right Haar-L² physical source. No independent conditional Haar
substitution and NO extra source-frame or source-separation assumptions.

We avoid assuming an artificial normed-space structure on the
physical visible Hilbert submodule. Instead, use the genuine source
synthesis S : E →ₗ Phys to choose a right-inverse linear section
R : range S →ₗ E. Its restriction A to the ACTUAL Hilbert-orthogonal
visible physical sector has S(A f)=f.

The finite-dimensional coefficient submodule W=range A is a coordinate
realization of exactly the true physical visible subspace. Both genuine
Gram quadratic forms are strictly positive on W\{0} by IM/IP and
the original Wilson GL Gram and source-Gram identities. The pinned
finite-dimensional comparison lemma then yields model-dependent
c,C>0 with
  c ‖f‖² ≤ originalWilsonGLMass(f) ≤ C ‖f‖²
for EACH actual physical f in the orthogonal visible sector.

These c,C may depend on volume, coupling, n, r, and geometry; this is
NOT H1-C3 closure or volume/spacing/depth-uniform Yang--Mills mass gap.
The invisible physical sector I_phys=S(K) is NOT proven to vanish.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IQ_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every genuine real linear source image has a linear coefficient
section, obtained from the pinned mathlib right-inverse of the
surjective range-restriction map. No injectivity of S is assumed. -/
noncomputable def p4Q2IQ_abstract_sourceRangeCoefficientSection
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (S : E →ₗ[ℝ] F) :
    S.range →ₗ[ℝ] E :=
  Classical.choose
    (S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict)

/-- Genuine physicalization of the chosen coefficient section is
exactly the original source. -/
theorem p4Q2IQ_abstract_sourceRangeCoefficientSection_rightInverse
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (S : E →ₗ[ℝ] F) (f : S.range) :
    S (p4Q2IQ_abstract_sourceRangeCoefficientSection S f) = (f : F) := by
  have h := LinearMap.congr_fun
    (Classical.choose_spec
      (S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict)) f
  have hf :
      S.rangeRestrict (p4Q2IQ_abstract_sourceRangeCoefficientSection S f) = f := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply,
      p4Q2IQ_abstract_sourceRangeCoefficientSection] using h
  exact congrArg Subtype.val hf

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Visible" =>
  p4Q2IM_actualRightVisiblePhysicalSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- The original fine-right coefficient representation of the
ACTUAL orthogonal visible physical source, selected linearly via the
source synthesis range section (without source injectivity). -/
noncomputable def p4Q2IQ_actualRightVisibleCoefficientSection :
    ↥Visible →ₗ[ℝ] Coeff := by
  have hV : Visible ≤ (PhysicalSource).range := by
    change Invisibleᗮ ⊓ (PhysicalSource).range ≤ (PhysicalSource).range
    exact inf_le_right
  exact (p4Q2IQ_abstract_sourceRangeCoefficientSection PhysicalSource).comp
    ((Visible).inclusion hV)

local notation "Section" =>
  p4Q2IQ_actualRightVisibleCoefficientSection
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Reconstruct EXACTLY the same physical Haar-L² source from its
chosen coefficient representative, for every actual visible source. -/
theorem p4Q2IQ_actualRightVisibleCoefficientSection_source
    (f : ↥Visible) :
    PhysicalSource (Section f) = (f : Phys) := by
  have hV : Visible ≤ (PhysicalSource).range := by
    change Invisibleᗮ ⊓ (PhysicalSource).range ≤ (PhysicalSource).range
    exact inf_le_right
  exact p4Q2IQ_abstract_sourceRangeCoefficientSection_rightInverse
    PhysicalSource ⟨(f : Phys), hV f.property⟩

/-- Positive physical Haar-L² quadratic norm and ORIGINAL interacting
Wilson GL Gram compare with fixed strictly positive constants on
every ACTUAL orthogonally GI-visible physical source. Crucially,
the lifted coefficient section allows use of the proven pinned
matrix/quadratic finite-dimensional norm comparison, instead of
postulating a physical frame or typeclass-invented norm structure. -/
theorem p4Q2IQ_actualVisible_originalGL_physicalSourceNorm_comparison
    (hFrozen : 0 < beta n) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ f : ↥Visible,
        c * ‖(f : Phys)‖ ^ 2 ≤
          OriginalMass (f : Phys) (Finset.univ : Finset Link) ∧
        OriginalMass (f : Phys) (Finset.univ : Finset Link) ≤
          C * ‖(f : Phys)‖ ^ 2 := by
  let A : ↥Visible →ₗ[ℝ] Coeff := Section
  let W : Submodule ℝ Coeff := A.range
  have hA (f : ↥Visible) :
      PhysicalSource (A f) = (f : Phys) :=
    p4Q2IQ_actualRightVisibleCoefficientSection_source
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r f
  have hWVisible (w : W) :
      PhysicalSource (w : Coeff) ∈ Visible := by
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp w.property
    have hSource : PhysicalSource (w : Coeff) = (f : Phys) :=
      (congrArg PhysicalSource hf.symm).trans (hA f)
    rw [hSource]
    exact f.property
  have hWSourceNonzero (w : W) (hw : w ≠ 0) :
      PhysicalSource (w : Coeff) ≠ 0 := by
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp w.property
    intro hSw
    have hSource : PhysicalSource (A f) = 0 := by
      rw [hf]
      exact hSw
    have hfPhys : (f : Phys) = 0 := (hA f).symm.trans hSource
    have hfZero : f = 0 := Subtype.ext hfPhys
    apply hw
    apply Subtype.ext
    calc
      (w : Coeff) = A f := hf.symm
      _ = A 0 := congrArg A hfZero
      _ = 0 := map_zero A
  let qB : W → ℝ :=
    fun w => star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff))
  let qS : W → ℝ :=
    fun w => star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff))
  have hContB : Continuous qB :=
    (p4Q2HR_realMatrix_quad_continuous (B hFrozen)).comp
      continuous_subtype_val
  have hContS : Continuous qS :=
    (p4Q2HR_realMatrix_quad_continuous Qsrc).comp
      continuous_subtype_val
  have hHomB (c : ℝ) (w : W) :
      qB (c • w) = c ^ 2 * qB w := by
    simpa only [qB, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul (B hFrozen) c (w : Coeff))
  have hHomS (c : ℝ) (w : W) :
      qS (c • w) = c ^ 2 * qS w := by
    simpa only [qS, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul Qsrc c (w : Coeff))
  have hPosB (w : W) (hw : w ≠ 0) : 0 < qB w := by
    dsimp only [qB]
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (w : Coeff)]
    exact p4Q2IM_actualVisibleSource_originalWilsonGLMass_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (PhysicalSource (w : Coeff))
      (hWVisible w) (hWSourceNonzero w hw)
  have hPosS (w : W) (hw : w ≠ 0) : 0 < qS w := by
    dsimp only [qS]
    rw [p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (w : Coeff)]
    exact pow_pos (norm_pos_iff.mpr (hWSourceNonzero w hw)) 2
  obtain ⟨c, C, hc, hcC, hComp⟩ :=
    p4Q2HR_finiteDimensional_positive_quadratics_comparable
      qB qS hContB hContS hHomB hHomS hPosB hPosS
  refine ⟨c, C, hc, hcC, ?_⟩
  intro f
  let w : W := ⟨A f, (LinearMap.mem_range).mpr ⟨f, rfl⟩⟩
  have hB :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (w : Coeff)
  have hS :=
    p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (w : Coeff)
  have hSource : PhysicalSource (w : Coeff) = (f : Phys) := hA f
  have hOnCoeff :
      c * ‖PhysicalSource (w : Coeff)‖ ^ 2 ≤
        OriginalMass (PhysicalSource (w : Coeff))
          (Finset.univ : Finset Link) ∧
      OriginalMass (PhysicalSource (w : Coeff))
          (Finset.univ : Finset Link) ≤
        C * ‖PhysicalSource (w : Coeff)‖ ^ 2 := by
    simpa only [qB, qS, hB, hS] using hComp w
  simpa only [hSource] using hOnCoeff

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IQ_abstract_sourceRangeCoefficientSection_rightInverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IQ_actualRightVisibleCoefficientSection_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IQ_actualVisible_originalGL_physicalSourceNorm_comparison
