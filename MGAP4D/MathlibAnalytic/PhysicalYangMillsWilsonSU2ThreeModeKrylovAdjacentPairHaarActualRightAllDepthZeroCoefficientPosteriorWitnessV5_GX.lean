import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUnitKrylovTransferPositiveV5_GV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedSourcePosteriorMassTransferKernelV5_GW
import Mathlib.Tactic

/-!
# P4-Q2-GX: a genuine original-Wilson all-finite-depth coefficient-space witness

GV establishes strictly positive ORIGINAL interacting Wilson identity-left
conditional posterior squared mass of the actual fine RIGHT Krylov depth-zero
source. GW supplies its genuine signed original-Wilson transfer-kernel
detection obstruction. Here put this concrete nonzero physical source
inside the ACTUAL arbitrary finite-depth right Krylov coefficient space,
with no surrogate finite-dimensional receiver.

For every finite r, use the explicit real coefficient vector a(j)=1 if
j=0 and 0 otherwise. Prove the genuine physical coefficient sum equals the
fine right Krylov zero-depth mode, which is itself the true physical
gauge-invariant constant unit independent of fine beta(n+1). The original
frozen beta(n) Wilson transfer is positive at EVERY right configuration.
For positive frozen beta(n), the original signed two-LEFT-boundary receiver
has positive Haar squared mass and the actual INTERACTING original Wilson
conditional posterior has strictly positive squared mass, uniformly over
the choice of physical right background and link (positivity, NOT a
quantitative r/H/n-uniform numerical bound).

Thus the coefficient-space transfer zero-locus and genuine Wilson
posterior squared-mass zero-locus are proper subsets of the actual
finite-depth coefficient space. This is a constructive existence theorem
for a detected coefficient vector at every r, NOT signed-source-frame
injectivity for every coefficient vector, GI's distinct two-posterior
signed expectation gap Delta, H1-C3, or the continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

section ActualAdjacent

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

/-- The actual depth-r real coefficient vector selecting exactly the
genuine fine right-Krylov zero-depth physical source. -/
def p4Q2GX_rightZeroCoefficient (r : ℕ) : Fin (r + 1) → ℝ :=
  fun j => if j = 0 then 1 else 0

theorem p4Q2GX_rightZeroCoefficient_at_zero :
    p4Q2GX_rightZeroCoefficient r (0 : Fin (r + 1)) = 1 := by
  simp [p4Q2GX_rightZeroCoefficient]

theorem p4Q2GX_rightZeroCoefficient_else_zero
    (j : Fin (r + 1)) (hj : j ≠ 0) :
    p4Q2GX_rightZeroCoefficient r j = 0 := by
  simp [p4Q2GX_rightZeroCoefficient, hj]

/-- Exact source identity INSIDE the real physical gauge-invariant Hilbert
submodule: the coefficient sum is not an abstract formal vector. -/
theorem p4Q2GX_actualRightCoefficientSource_eq_zeroMode :
    (∑ j : Fin (r + 1),
      p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ)) =
      RightFactor n 0 := by
  classical
  let a := p4Q2GX_rightZeroCoefficient r
  change (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) =
    RightFactor n 0
  calc
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) =
        a (0 : Fin (r + 1)) • RightFactor n 0 := by
      apply Finset.sum_eq_single (0 : Fin (r + 1))
      · intro j _hj hj
        simp [a, p4Q2GX_rightZeroCoefficient, hj]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    _ = RightFactor n 0 := by
      simp [a, p4Q2GX_rightZeroCoefficient]

/-- The zero-selector physical source is the literal normalized physical
constant unit at fine beta(n+1), not a surrogate coefficient vector. -/
theorem p4Q2GX_actualRightCoefficientSource_eq_physicalUnit :
    (∑ j : Fin (r + 1),
      p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2 := by
  calc
    _ = RightFactor n 0 :=
      p4Q2GX_actualRightCoefficientSource_eq_zeroMode
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2 :=
      fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta n

/-- The genuine signed-source original Wilson transfer on this concrete
all-depth coefficient vector is STRICTLY positive at every physical
right boundary, without any positive-source assumption. -/
theorem p4Q2GX_actualRightZeroCoefficient_originalTransfer_pos (B : Cfg) :
    0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1),
        p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ)) B := by
  have hPhysical :
      (∑ j : Fin (r + 1),
        p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ)) =
        RightFactor n 0 :=
    p4Q2GX_actualRightCoefficientSource_eq_zeroMode
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hLp :
      (∑ j : Fin (r + 1),
        p4Q2GX_rightZeroCoefficient r j •
          (RightFactor n (j : ℕ) : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2))) =
        (RightFactor n 0 : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2)) := by
    have h := congrArg Subtype.val hPhysical
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  rw [hLp]
  exact p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n B

/-- The literal two original physical left boundaries give a strictly
positive SU(2) Haar REFERENCE squared physical receiver contrast. -/
theorem p4Q2GX_actualRightZeroCoefficient_HaarMass_pos
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1),
        p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ))
      right e := by
  rw [p4Q2GX_actualRightCoefficientSource_eq_zeroMode
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r]
  exact p4Q2GV_actualFineRightZeroMode_twoBoundaryHaarMass_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen right e

/-- Preserve the actual interacting Wilson posterior rather than
incorrectly identifying it with independent Haar. -/
theorem p4Q2GX_actualRightZeroCoefficient_PosteriorMass_ge_Haar
    (right : Cfg) (e : Link) :
    Real.exp (-16 * beta n) *
        p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1),
            p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ))
          right e ≤
      p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1),
          p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ))
        right e := by
  exact p4Q2GU_originalPhysicalContrastPosteriorMass_ge_Haar
    Hn (beta n) (hbeta n)
    (∑ j : Fin (r + 1),
      p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ))
    right e

/-- A depth-r ACTUAL coefficient source has positive squared contrast
mass under the GENUINE interacting original Wilson conditional law. -/
theorem p4Q2GX_actualRightZeroCoefficient_PosteriorMass_pos
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1),
        p4Q2GX_rightZeroCoefficient r j • RightFactor n (j : ℕ))
      right e := by
  rw [p4Q2GX_actualRightCoefficientSource_eq_zeroMode
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r]
  exact p4Q2GV_actualFineRightZeroMode_twoBoundaryWilsonPosteriorMass_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen right e

/-- ONE fixed explicitly constructed coefficient vector simultaneously
works for EVERY actual right spatial configuration and every link. -/
theorem p4Q2GX_allFiniteDepth_exists_uniformly_detected_coefficient
    (hFrozen : 0 < beta n) :
    ∃ a : Fin (r + 1) → ℝ,
      ∀ (right : Cfg) (e : Link),
        0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
          right e := by
  refine ⟨p4Q2GX_rightZeroCoefficient r, ?_⟩
  intro right e
  exact p4Q2GX_actualRightZeroCoefficient_PosteriorMass_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen right e

/-- The actual signed transfer zero-locus cannot be the ENTIRE
finite-depth real coefficient space. This is properness, not injectivity. -/
theorem p4Q2GX_actualRightCoefficientTransfer_zeroLocus_proper (B : Cfg) :
    ¬ ∀ a : Fin (r + 1) → ℝ,
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B = 0 := by
  intro hAll
  have hPos :=
    p4Q2GX_actualRightZeroCoefficient_originalTransfer_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r B
  exact (ne_of_gt hPos) (hAll (p4Q2GX_rightZeroCoefficient r))

/-- At every positive frozen beta, zero squared mass under the actual
Wilson posterior does not hold for ALL coefficient vectors. This does
not claim that its zero-locus consists only of the zero vector. -/
theorem p4Q2GX_actualRightCoefficientPosteriorMass_zeroLocus_proper
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ¬ ∀ a : Fin (r + 1) → ℝ,
      p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        right e = 0 := by
  intro hAll
  have hPos :=
    p4Q2GX_actualRightZeroCoefficient_PosteriorMass_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen right e
  exact (ne_of_gt hPos) (hAll (p4Q2GX_rightZeroCoefficient r))

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_rightZeroCoefficient_at_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_rightZeroCoefficient_else_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightCoefficientSource_eq_zeroMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightZeroCoefficient_originalTransfer_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightZeroCoefficient_HaarMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightZeroCoefficient_PosteriorMass_ge_Haar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightZeroCoefficient_PosteriorMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_allFiniteDepth_exists_uniformly_detected_coefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightCoefficientTransfer_zeroLocus_proper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GX_actualRightCoefficientPosteriorMass_zeroLocus_proper
