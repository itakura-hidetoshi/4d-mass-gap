import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonKernelWeightedEnergyV5_KC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonReceiverKernelMomentV5_KB
import Mathlib.Tactic

/-!
# P4-Q2-KD — proved nondegeneracy of the original Wilson spatial two-mode kernel Gram matrix

The original Wilson one-slab kernel K_b(A,B) and original spatial product
SU(2) Haar are NOT replaced. KC proves strict positive K_b-weighted
squared energy of W_H-c for every real c and every physical boundary B.

We now identify the three literal original Wilson kernel moments
 m_0(B) = integral K_b(A,B),
 m_1(B) = integral K_b(A,B) W_H(A),
 m_2(B) = integral K_b(A,B) W_H(A)^2.
Using full-support Haar and KC (not any rank hypothesis), we prove
 m_0(B)>0 and m_0(B)*m_2(B)-m_1(B)^2>0
for all real b, finite H, and physical B.

Consequently at every B, no choice of center c can make BOTH the
original centered Wilson zeroth and first Wilson-inserted moments zero:
 (m_1-c*m_0, m_2-c*m_1) != (0,0).
This is an authentic Wilson action two-mode detection statement, NOT
the unresolved signed two-interacting-posterior GI response, which
involves SU(2) link insertion, Perron square roots, and signed
posterior differences. No independent-Haar posterior, source-frame
assumption, new axiom/sorry/admit, H1-C3, or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2KD_su2HaarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2KD_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section Finite
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "W" => p4Q2JI_actualSpatialWilsonContinuous H

/-- Positivity of the LITERAL original Wilson kernel's spatial Haar mass
at any physical right boundary, without a normalization substitution. -/
theorem p4Q2KD_originalWilsonSpatialKernelMass_pos
    (b : ℝ) (B : Cfg) :
    0 < p4Q2KB_originalSpatialWilsonKernelMass H b B := by
  have hCont : Continuous (fun A : Cfg => K b A B) := by
    simpa only [p4Q2KC_originalWilsonKernelColumn_apply] using
      (p4Q2KC_originalWilsonKernelColumn H b B).continuous
  have hI : Integrable (fun A : Cfg => K b A B) haar :=
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hOpen : IsOpen (Function.support (fun A : Cfg => K b A B)) := by
    change IsOpen ((fun A : Cfg => K b A B) ⁻¹' ({0} : Set ℝ)ᶜ)
    exact (isClosed_singleton.isOpen_compl).preimage hCont
  unfold p4Q2KB_originalSpatialWilsonKernelMass
  rw [integral_pos_iff_support_of_nonneg]
  · apply hOpen.measure_pos
    exact ⟨(fun _ : Link => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b (fun _ => 1) B).ne'⟩
  · intro A
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A B).le
  · exact hI

/-- The actual second spatial Wilson-action moment of the same original
one-slab kernel and the same spatial Haar reference as KB and KC. -/
noncomputable def p4Q2KD_originalWilsonSpatialKernelSquareMoment
    (b : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, K b A B * (W A) ^ 2 ∂haar

/-- Exact centered-square polynomial expansion in the THREE ORIGINAL
Wilson spatial kernel moments. All terms are integrable by continuity
on the compact genuine SU(2) spatial configuration space. -/
theorem p4Q2KD_originalWilsonCenteredEnergy_momentExpansion
    (b : ℝ) (B : Cfg) (c : ℝ) :
    (∫ A : Cfg, K b A B * (W A - c) ^ 2 ∂haar) =
      p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B -
        (2 * c) * p4Q2KB_originalSpatialWilsonActionKernelMoment H b B +
        c ^ 2 * p4Q2KB_originalSpatialWilsonKernelMass H b B := by
  have hKCont : Continuous (fun A : Cfg => K b A B) := by
    simpa only [p4Q2KC_originalWilsonKernelColumn_apply] using
      (p4Q2KC_originalWilsonKernelColumn H b B).continuous
  have hKWCont : Continuous (fun A : Cfg => K b A B * W A) :=
    hKCont.mul W.continuous
  have hKW2Cont : Continuous (fun A : Cfg => K b A B * (W A) ^ 2) :=
    hKCont.mul (W.continuous.pow 2)
  have hK : Integrable (fun A : Cfg => K b A B) haar :=
    hKCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKW : Integrable (fun A : Cfg => K b A B * W A) haar :=
    hKWCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKW2 : Integrable (fun A : Cfg => K b A B * (W A) ^ 2) haar :=
    hKW2Cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, K b A B * (W A - c) ^ 2 ∂haar) =
        ∫ A : Cfg,
          (K b A B * (W A) ^ 2 - (2 * c) * (K b A B * W A)) +
            c ^ 2 * K b A B ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = _ := by
      rw [integral_add (hKW2.sub (hKW.const_mul (2 * c)))
        (hK.const_mul (c ^ 2))]
      rw [integral_sub hKW2 (hKW.const_mul (2 * c))]
      simp only [integral_const_mul]
      rfl

/-- Strict determinant of the TRUE Wilson-weighted Gram matrix
for the physical spatial functions 1 and W_H, at EVERY B and b.
The rank-two conclusion is PROVED by KC's original-kernel positivity,
not introduced as an artificial rank or detector assumption. -/
theorem p4Q2KD_originalWilsonSpatialKernelGramDet_pos
    (b : ℝ) (B : Cfg) :
    0 <
      p4Q2KB_originalSpatialWilsonKernelMass H b B *
        p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B -
      (p4Q2KB_originalSpatialWilsonActionKernelMoment H b B) ^ 2 := by
  let m0 : ℝ := p4Q2KB_originalSpatialWilsonKernelMass H b B
  let m1 : ℝ := p4Q2KB_originalSpatialWilsonActionKernelMoment H b B
  let m2 : ℝ := p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B
  have hm0 : 0 < m0 :=
    p4Q2KD_originalWilsonSpatialKernelMass_pos H b B
  have hKC := p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
    H b B (m1 / m0)
  rw [p4Q2KD_originalWilsonCenteredEnergy_momentExpansion] at hKC
  change 0 < m2 - (2 * (m1 / m0)) * m1 + (m1 / m0) ^ 2 * m0 at hKC
  have hProd :
      0 < m0 * (m2 - (2 * (m1 / m0)) * m1 + (m1 / m0) ^ 2 * m0) :=
    mul_pos hm0 hKC
  have hAlg :
      m0 * (m2 - (2 * (m1 / m0)) * m1 + (m1 / m0) ^ 2 * m0) =
        m0 * m2 - m1 ^ 2 := by
    field_simp [ne_of_gt hm0]
    <;> ring
  rw [hAlg] at hProd
  change 0 < m0 * m2 - m1 ^ 2
  exact hProd

/-- A genuine original Wilson spatial two-mode non-cancellation theorem.
The two moments are the coefficients of the original centered source
against the actual Wilson kernel with insertions 1 and W_H.
This is NOT yet nonzero two-interacting-posterior GI response. -/
theorem p4Q2KD_originalWilsonSpatialTwoMode_noSimultaneousCancellation
    (b : ℝ) (B : Cfg) (c : ℝ) :
    (p4Q2KB_originalSpatialWilsonActionKernelMoment H b B -
        c * p4Q2KB_originalSpatialWilsonKernelMass H b B ≠ 0) ∨
      (p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B -
        c * p4Q2KB_originalSpatialWilsonActionKernelMoment H b B ≠ 0) := by
  let m0 : ℝ := p4Q2KB_originalSpatialWilsonKernelMass H b B
  let m1 : ℝ := p4Q2KB_originalSpatialWilsonActionKernelMoment H b B
  let m2 : ℝ := p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B
  have hDet := p4Q2KD_originalWilsonSpatialKernelGramDet_pos H b B
  change 0 < m0 * m2 - m1 ^ 2 at hDet
  change (m1 - c * m0 ≠ 0) ∨ (m2 - c * m1 ≠ 0)
  by_cases hFirst : m1 - c * m0 = 0
  · right
    intro hSecond
    have h1 : m1 = c * m0 := sub_eq_zero.mp hFirst
    have h2 : m2 = c * m1 := sub_eq_zero.mp hSecond
    have hZero : m0 * m2 - m1 ^ 2 = 0 := by
      rw [h2, h1]
      ring
    exact (ne_of_gt hDet) hZero
  · exact Or.inl hFirst

end Finite
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KD_originalWilsonSpatialKernelMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KD_originalWilsonCenteredEnergy_momentExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KD_originalWilsonSpatialKernelGramDet_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KD_originalWilsonSpatialTwoMode_noSimultaneousCancellation
