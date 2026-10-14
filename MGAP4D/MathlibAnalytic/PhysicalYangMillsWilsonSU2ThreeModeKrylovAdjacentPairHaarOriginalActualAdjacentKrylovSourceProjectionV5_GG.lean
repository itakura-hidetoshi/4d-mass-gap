import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSourceProjectionGramRayleighV5_GE
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInputRayleigh
import Mathlib.Tactic

/-!
# P4-Q2-GG: actual adjacent-scale right-Krylov / left-three-mode Wilson Gram floor

GE certifies the genuine source-dependent Wilson Gram Rayleigh lower
bound for EVERY finite original physical Hilbert source family.

Here the source family is no longer an arbitrary named family: use the
EXACT existing physical adjacent-scale right Krylov orbit
  RightFactor(n,j) = S_fine(beta(n+1))^j applied to the canonical input
and the EXACT three physical left Gram-Schmidt factors
  LeftFactor(n,r,k).

The original physical posterior, Gram projections, source overlap, and
transfer normalization all use the FROZEN coupling beta(n) on volume
Hn=halfExtent(n+1). The micro/fine beta(n+1) is retained INSIDE the true
RightFactor/LeftFactor definitions and is never identified with beta(n).

Prove the quantitative source projection Rayleigh certificate for both
original Gram matrices. Also expose explicit source-frame hypotheses
for the corresponding coefficient Rayleigh floors, without asserting
either source-frame premise.

No independent conditional Haar posterior, Dobrushin, artificial
orthogonalized source, scale-uniform summability, H1-C3 closure, or
continuum mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

namespace GroundStatePosteriorJoint

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The REAL original (r+1)-mode right Krylov Gram at frozen beta(n)
inherits GE's physical Wilson signed source projection certificate.
The orbit itself still uses its actual fine beta(n+1). -/
theorem p4Q2GG_actualFineRightKrylovGram_ge_sourceProjection
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 Pos (beta n) (hbeta n)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta n) *
        (Real.exp (-32 * beta n) *
          ((beta n) ^ 2 *
            p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
          (Finset.univ : Finset Link)) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  simpa only [fineRightKrylovPairHaarResidualGram] using
    (p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
      Hn (beta n) hFrozen
      (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a)

/-- The ORIGINAL left three-mode Gram-Schmidt physical source family
receives the identical quantitative frozen-posterior projected mass
certificate without replacing its actual fine-evolved source factors. -/
theorem p4Q2GG_actualFineLeftThreeModeGram_ge_sourceProjection
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 Pos (beta n) (hbeta n)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta n) *
        (Real.exp (-32 * beta n) *
          ((beta n) ^ 2 *
            p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          Hn (beta n) (hbeta n)
          (∑ k : Fin 3, a k • LeftFactor n r k)
          (Finset.univ : Finset Link)) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  simpa only [fineLeftThreeModePairHaarResidualGram] using
    (p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
      Hn (beta n) hFrozen
      (fun k : Fin 3 => LeftFactor n r k) a)

/-- EXACT missing finite right-Krylov frame input stated explicitly:
a physically established gamma-H lower source-projection bound is
sufficient for the corresponding genuine Wilson Gram Rayleigh bound. -/
theorem p4Q2GG_actualFineRightKrylovGram_ge_of_sourceFrame
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) (gamma : ℝ)
    (hFrame : gamma * (∑ j : Fin (r + 1), (a j) ^ 2) ≤
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link)) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 Pos (beta n) (hbeta n)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta n) *
        (Real.exp (-32 * beta n) *
          ((beta n) ^ 2 *
            p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        (gamma * (∑ j : Fin (r + 1), (a j) ^ 2))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  simpa only [fineRightKrylovPairHaarResidualGram] using
    (p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_of_sourceFrame
      Hn (beta n) hFrozen
      (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a gamma hFrame)

/-- The same genuine physical source-frame obligation specialized to the
ACTUAL three left Gram-Schmidt modes of the fine-to-frozen comparison. -/
theorem p4Q2GG_actualFineLeftThreeModeGram_ge_of_sourceFrame
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) (gamma : ℝ)
    (hFrame : gamma * (∑ k : Fin 3, (a k) ^ 2) ≤
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        (Finset.univ : Finset Link)) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 Pos (beta n) (hbeta n)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta n) *
        (Real.exp (-32 * beta n) *
          ((beta n) ^ 2 *
            p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        (gamma * (∑ k : Fin 3, (a k) ^ 2))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  simpa only [fineLeftThreeModePairHaarResidualGram] using
    (p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_of_sourceFrame
      Hn (beta n) hFrozen
      (fun k : Fin 3 => LeftFactor n r k) a gamma hFrame)

end ActualAdjacentOrbit

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GG_actualFineRightKrylovGram_ge_sourceProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GG_actualFineLeftThreeModeGram_ge_sourceProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GG_actualFineRightKrylovGram_ge_of_sourceFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GG_actualFineLeftThreeModeGram_ge_of_sourceFrame
