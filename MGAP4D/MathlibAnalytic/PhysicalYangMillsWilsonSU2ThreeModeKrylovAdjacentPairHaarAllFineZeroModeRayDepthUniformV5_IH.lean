import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGLPhysicalSourceNormOnGIComplementV5_IG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroDepthUniformPhysicalSourceNormV5_IF
import Mathlib.Tactic

/-!
# P4-Q2-IH: depth-uniform original Wilson zero-mode ray for ALL fine couplings

IE and IB prove fixed-finite-model ORIGINAL GL mass coercivity against
the genuine physical Haar-L² source norm for the single zero-depth
right-Krylov mode, with positive frozen Wilson beta(n)>0 and ANY
nonnegative fine beta(n+1).

IF gives the same two-sided physical source-norm bounds at ALL Krylov
depths only when fine beta(n+1)=0. Here the fine-beta restriction is
removed on the genuine all-depth ZERO-MODE COEFFICIENT RAY:
  a_j = t * 1_{j=0}.
GX proves that every such all-depth source is the same actual physical
unit source; the scalar t is its true physical Hilbert coefficient.
This source identity is independent of fine beta(n+1), even if it is
strictly positive.

Consequently the very SAME positive frozen-model constants c,C from
the genuine one-mode original-Wilson comparison work simultaneously
for every depth r and scalar t on this explicit ray, with a genuine
physical source norm, and in fact
  c*t^2 <= M_GL(t*unit) <= C*t^2.
No source independence or full higher-depth source-frame property is
assumed. The claim is precisely one distinguished physical ray at
every depth, not the entire (r+1)-dimensional coefficient space;
neither volume/spacing/frozen-coupling uniformity nor continuum
Yang--Mills mass gap follows.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2IH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IH_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section TrueZeroModeRay

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- At EVERY finite depth r and nonnegative fine beta(n+1), the
scaled genuine GX zero-selector is EXACTLY the corresponding actual
one-mode physical source, inside the original physical Haar-L²
gauge-invariant Hilbert submodule. -/
theorem p4Q2IH_allFine_actualRight_scaledZeroSelector_source_eq_oneMode
    (r : ℕ) (t : ℝ) :
    (∑ j : Fin (r + 1),
      (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ)) =
      (∑ j : Fin (0 + 1),
        (fun _ : Fin (0 + 1) => t) j • RightFactor n (j : ℕ)) := by
  have hRay :
      (∑ j : Fin (r + 1),
        (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ)) =
        t • RightFactor n 0 := by
    calc
      (∑ j : Fin (r + 1),
        (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ)) =
          ∑ j : Fin (r + 1),
            t • (p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ)) := by
              simp only [mul_smul]
      _ = t • (∑ j : Fin (r + 1),
          p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ)) := by
            rw [Finset.smul_sum]
      _ = t • RightFactor n 0 := by
        rw [p4Q2GX_actualRightCoefficientSource_eq_zeroMode
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r]
  have hOne :
      (∑ j : Fin (0 + 1),
        (fun _ : Fin (0 + 1) => t) j • RightFactor n (j : ℕ)) =
        t • RightFactor n 0 := by
    change (∑ j : Fin 1, t • RightFactor n (j : ℕ)) =
      t • RightFactor n 0
    simp only [Fin.sum_univ_one, Fin.val_zero]
  exact hRay.trans hOne.symm

/-- The original, actual physical source norm on the explicit
zero-mode ray is EXACTLY the absolute scalar t, so the source norm
squared equals t squared. No coefficient frame is assumed. -/
theorem p4Q2IH_allFine_actualRight_scaledZeroSelector_sourceNorm_sq
    (r : ℕ) (t : ℝ) :
    ‖∑ j : Fin (r + 1),
      (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ)‖ ^ 2 =
        t ^ 2 := by
  rw [p4Q2IH_allFine_actualRight_scaledZeroSelector_source_eq_oneMode
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r t]
  change ‖∑ j : Fin 1, t • RightFactor n (j : ℕ)‖ ^ 2 = t ^ 2
  simp only [Fin.sum_univ_one, Fin.val_zero]
  rw [norm_smul]
  rw [fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm Hn 2]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]

/-- Unlike IF's all-coefficient statement (which needs fine beta=0),
the SAME positive one-mode Wilson constants work for the explicitly
scaled physical zero-mode ray at EVERY fine coupling and EVERY finite
Krylov depth. The constants are independent of r and the scalar t. -/
theorem p4Q2IH_allFine_actualRight_zeroRay_GL_physicalNorm_depthUniform
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (r : ℕ) (t : ℝ),
        c * ‖∑ j : Fin (r + 1),
          (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ)‖ ^ 2 ≤
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1),
              (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1),
              (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ≤
          C * ‖∑ j : Fin (r + 1),
            (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ)‖ ^ 2 := by
  obtain ⟨c, C, hc, hcC, hZero⟩ :=
    p4Q2IE_depthZero_originalWilsonGLMass_physicalSourceNorm_fixed_comparison
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨c, C, hc, hcC, ?_⟩
  intro r t
  have hSource :=
    p4Q2IH_allFine_actualRight_scaledZeroSelector_source_eq_oneMode
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r t
  simpa only [hSource] using hZero (fun _ : Fin (0 + 1) => t)

/-- Quantitative original GL mass scalar-ray bounds for all Krylov
depths at ANY nonnegative fine coupling, with identical c,C at
fixed finite physical volume and frozen Wilson beta. No estimate
in the full coefficient norm for arbitrary signed vectors is claimed. -/
theorem p4Q2IH_allFine_actualRight_zeroRay_GL_scalarSquare_depthUniform
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (r : ℕ) (t : ℝ),
        c * t ^ 2 ≤
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1),
              (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1),
              (t * p4Q2GX_rightZeroCoefficient r j) • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ≤
          C * t ^ 2 := by
  obtain ⟨c, C, hc, hcC, hComp⟩ :=
    p4Q2IH_allFine_actualRight_zeroRay_GL_physicalNorm_depthUniform
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨c, C, hc, hcC, ?_⟩
  intro r t
  have hBounds := hComp r t
  rw [p4Q2IH_allFine_actualRight_scaledZeroSelector_sourceNorm_sq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r t] at hBounds
  exact hBounds

end TrueZeroModeRay
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IH_allFine_actualRight_scaledZeroSelector_source_eq_oneMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IH_allFine_actualRight_scaledZeroSelector_sourceNorm_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IH_allFine_actualRight_zeroRay_GL_physicalNorm_depthUniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IH_allFine_actualRight_zeroRay_GL_scalarSquare_depthUniform
