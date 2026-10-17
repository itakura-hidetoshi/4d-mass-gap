import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonCrossingMeanInvariantV5_IX
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonCenterWitnessV5_IY
import MGAP4D.MathlibAnalytic.NonzeroDerivativeSmallPositive
import Mathlib.Tactic

/-!
# P4-Q2-IZ: actual Wilson Haar row is nonconstant at small positive coupling

At every genuine finite SU(2) even-periodic spatial volume H:

1. IX differentiates the **original** Wilson one-slab Haar row at beta=0,
   and proves that the difference of two row derivatives is exactly minus
   one half of the original spatial-plaquette Wilson action difference.
2. IY constructs two literal physical right spatial boundaries: all identity
   and the primary-plaquette one-link SU(2) central (-I) twist. The actual
   spatial Wilson actions differ by at least 2.
3. The repository's pinned-mathlib small-positive-beta calculus lemma
   converts a nonzero derivative and zero value at beta=0 into a genuine
   nonzero Wilson Haar row contrast throughout some (0,epsilon).
4. IV transports the resulting literal two-right-boundary contrast to
   noncollinearity of the actual first fine-right physical Krylov source
   with the physical Haar constant unit.

The result is local in beta at each fixed finite H. The positive radius is
NOT claimed to be H/scale/spacing-uniform, and this does NOT prove genuine
interacting-Wilson two-posterior GI 2-context minor nondegeneracy, H1-C3,
4D continuum Yang-Mills construction or the Clay mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped Topology

noncomputable section
set_option maxHeartbeats 2600000

namespace GroundStatePosteriorJoint

section RawWilsonSmallBeta

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "F" =>
  p4Q2IV_originalWilsonUnitHaarKernelSection H

/-- A genuine nonzero spatial-Wilson action difference between two real
boundaries forces their literal original one-slab Haar rows to differ for
ALL sufficiently small strictly positive beta. -/
theorem p4Q2IZ_originalWilsonHaarRow_smallPositive_of_spatialAction_ne
    (B₀ B₁ : Cfg) (hW : W B₀ ≠ W B₁) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ beta : ℝ, 0 < beta → beta < ε → F beta B₀ ≠ F beta B₁ := by
  let f : ℝ → ℝ := fun beta => F beta B₀ - F beta B₁
  have hderiv :
      HasDerivAt f (-(1 / 2 : ℝ) * (W B₀ - W B₁)) 0 := by
    exact p4Q2IX_originalWilsonTwoRowDifference_hasDerivAt_zero H B₀ B₁
  have hzero : f 0 = 0 := by
    dsimp [f]
    rw [p4Q2IW_originalWilsonHaarRow_beta_zero H B₀,
      p4Q2IW_originalWilsonHaarRow_beta_zero H B₁]
    ring
  have hd : -(1 / 2 : ℝ) * (W B₀ - W B₁) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hW)
  rcases
      HasDerivAt.exists_pos_forall_pos_lt_ne_zero_of_eq_zero_of_ne_zero
        hderiv hzero hd with
    ⟨ε, hε, hnonzero⟩
  refine ⟨ε, hε, ?_⟩
  intro beta hpos hlt
  exact sub_ne_zero.mp (hnonzero beta hpos hlt)

/-- Unconditional *physical* two-boundary witness: for every finite even
periodic spatial volume, there exist two true SU(2) right configurations and
one strictly positive epsilon such that the ORIGINAL Wilson Haar rows differ
at every beta in (0,epsilon). No independent-posterior substitution. -/
theorem p4Q2IZ_originalWilsonHaarRow_smallPositive_twoBoundary_witness :
    ∃ B₀ B₁ : Cfg, ∃ ε : ℝ, 0 < ε ∧
      ∀ beta : ℝ, 0 < beta → beta < ε → F beta B₀ ≠ F beta B₁ := by
  rcases p4Q2IY_originalSpatialWilsonAction_not_constant H with
    ⟨B₀, B₁, hW⟩
  rcases
      p4Q2IZ_originalWilsonHaarRow_smallPositive_of_spatialAction_ne
        H B₀ B₁ hW with ⟨ε, hε, hsep⟩
  exact ⟨B₀, B₁, ε, hε, hsep⟩

/-- The same two original physical boundaries work simultaneously for the
entire interval of sufficiently small positive fine Wilson couplings. -/
theorem p4Q2IZ_originalWilsonHaarRow_smallPositive_not_constant :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ beta : ℝ, 0 < beta → beta < ε →
        ¬ ∃ c : ℝ, ∀ B : Cfg, F beta B = c := by
  rcases p4Q2IZ_originalWilsonHaarRow_smallPositive_twoBoundary_witness H with
    ⟨B₀, B₁, ε, hε, hsep⟩
  refine ⟨ε, hε, ?_⟩
  intro beta hpos hlt hconstant
  rcases hconstant with ⟨c, hc⟩
  exact (hsep beta hpos hlt) ((hc B₀).trans (hc B₁).symm)

end RawWilsonSmallBeta

section ActualPhysicalFine

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "FineTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))

/-- The physical content of IZ: for each fixed fine spatial extent,
there is a strictly positive beta window in which the TRUE normalized
fine Wilson transfer of the physical constant Haar-L² vector is NEVER
on its constant-unit eigenline. This is actual first-depth Krylov source
noncollinearity, not GI detector separation or a uniform mass-gap bound. -/
theorem p4Q2IZ_actualFineUnit_notEigenline_for_small_positive_beta :
    ∃ ε : ℝ, 0 < ε ∧
      (0 < beta (n + 1) → beta (n + 1) < ε →
        ¬ ∃ t : ℝ, FineTransfer Unit = t • Unit) := by
  rcases p4Q2IZ_originalWilsonHaarRow_smallPositive_twoBoundary_witness Hn with
    ⟨B₀, B₁, ε, hε, hsep⟩
  refine ⟨ε, hε, ?_⟩
  intro hpos hlt
  exact
    (p4Q2IV_actualFineUnit_notEigenline_iff_two_rawWilson_boundaries
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n).mpr
        ⟨B₀, B₁, hsep (beta (n + 1)) hpos hlt⟩

end ActualPhysicalFine

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IZ_originalWilsonHaarRow_smallPositive_of_spatialAction_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IZ_originalWilsonHaarRow_smallPositive_twoBoundary_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IZ_originalWilsonHaarRow_smallPositive_not_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IZ_actualFineUnit_notEigenline_for_small_positive_beta
