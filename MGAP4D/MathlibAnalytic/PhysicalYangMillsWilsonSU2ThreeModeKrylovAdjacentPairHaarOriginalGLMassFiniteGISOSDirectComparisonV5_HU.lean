import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLFiniteSOSGlobalComparisonV5_HT
import Mathlib.Tactic

/-!
# P4-Q2-HU: direct original Wilson GL mass versus genuine finite GI squares

HT proves a fixed-finite-model positive comparison of the ORIGINAL Wilson
GL integral detector Gram and HN's genuine finite GI square-sum Gram on ALL
signed adjacent fine-right Krylov coefficients.

Here the Gram variables are fully eliminated:
* HO identifies the quadratic GL Gram value with the physical spatial-link
  pair-Haar integral of (true interacting Wilson posterior gap)^2 divided
  by the original positive Wilson posterior density-contrast square.
* HN identifies the finite GI Gram value with the sum of squares of the
  SAME actual signed physical source's two-interacting-Wilson-posterior
  expectation gaps evaluated at finitely many real SU(2) physical contexts.

Thus the original physical mass and finite true GI expectations are
comparable above and below with positive constants for all signed source
coefficients in the FIXED model. The constants may depend on volume, n,
Krylov depth, frozen/fine couplings, and the chosen physical contexts.

No rank equality with the physical source Gram, source separation,
volume/scale/depth-uniform bounds, spatial summability, H1-C3, OS
Hamiltonian, or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HU_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "Context" => Link × Pair
local notation "μH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Gap" =>
  p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    Hn (beta n) (hbeta n)
local notation "Variance" =>
  p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    Hn (beta n) (hbeta n)
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- The actual GL spatial-link mass is directly comparable to a finite
sum of squares of the SAME original two-interacting-Wilson-posterior
expectation differences for every signed fine-right Krylov source. -/
theorem p4Q2HU_actualRight_originalWilson_GL_mass_GI_gap_squares_fixed_comparison
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * (∑ x : s,
          (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            x.1.1 x.1.2)^2) ≤
          OriginalMass
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
        OriginalMass
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ≤
          C * (∑ x : s,
            (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              x.1.1 x.1.2)^2) := by
  obtain ⟨c, C, hc, hcC, hBounds⟩ :=
    p4Q2HT_actualRight_originalWilson_GL_SOS_global_fixed_comparison
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen s hExact
  refine ⟨c, C, hc, hcC, ?_⟩
  intro a
  have hSOS :=
    p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_quad_eq_actualSourceGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s a
  have hGL :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a
  simpa only [hSOS, hGL] using hBounds a

/-- A formulation exposing the ACTUAL outer pair-Haar integrand.
Its denominator is the genuine positive frozen Wilson posterior
density-row contrast, not a synthetic Haar posterior or a variance
of the fine coupling. The source uses fine beta(n+1), separately. -/
theorem p4Q2HU_actualRight_originalWilson_GL_integral_GI_squares_fixed_comparison
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * (∑ x : s,
          (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            x.1.1 x.1.2)^2) ≤
          ∑ e : Link, ∫ z : Pair,
            (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              e z)^2 / Variance z.2 e ∂μH ∧
        (∑ e : Link, ∫ z : Pair,
            (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              e z)^2 / Variance z.2 e ∂μH) ≤
          C * (∑ x : s,
            (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              x.1.1 x.1.2)^2) := by
  obtain ⟨c, C, hc, hcC, hBounds⟩ :=
    p4Q2HU_actualRight_originalWilson_GL_mass_GI_gap_squares_fixed_comparison
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen s hExact
  refine ⟨c, C, hc, hcC, ?_⟩
  intro a
  simpa only [
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass,
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
  ] using hBounds a

/-- An HK exact finite physical-context certificate and positive
comparison constants exist jointly. They need NOT be numerical,
constructively enumerated, or uniform along lattice refinements. -/
theorem p4Q2HU_actualRight_exists_originalWilson_GL_mass_GI_squares_comparison
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ a : Coeff,
          c * (∑ x : s,
            (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              x.1.1 x.1.2)^2) ≤
            OriginalMass
              (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              (Finset.univ : Finset Link) ∧
          OriginalMass
              (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
              (Finset.univ : Finset Link) ≤
            C * (∑ x : s,
              (Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
                x.1.1 x.1.2)^2) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_⟩
  exact p4Q2HU_actualRight_originalWilson_GL_mass_GI_gap_squares_fixed_comparison
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen s hs

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HU_actualRight_originalWilson_GL_mass_GI_gap_squares_fixed_comparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HU_actualRight_originalWilson_GL_integral_GI_squares_fixed_comparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HU_actualRight_exists_originalWilson_GL_mass_GI_squares_comparison
