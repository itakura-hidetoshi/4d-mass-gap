import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGramDiagonalRayleighCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4: exact beta-zero collapse of the genuine right physical Krylov orbit

The previous P4 Gram results retain the ORIGINAL physical right factor

  R(n,r) = (S_(n+1,beta(n+1)))^r (constant physical unit).

At beta(n+1) = 0, the normalized physical transfer fixes this very
constant physical unit vector by the existing exact beta-zero rank-one
theorem. Consequently the ENTIRE actual right Krylov family is literally
constant in r, with no spatial-volume assumptions.

This is a structural endpoint statement, independent of frozen beta(n):
the original frozen posterior law, pair-Haar carrier and physical
half-density are NOT modified. The result does not imply a positive-beta
volume-uniform diagonal bound, or a continuum mass gap, and uses no
Dobrushin or positive-depth support assumption.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4BetaZeroRightTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4BetaZeroRightCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4BetaZeroRightSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4BetaZeroRightMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4BetaZeroRightBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4BetaZeroRightSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Abstract fixed-vector persistence under every natural power of an
actual continuous linear map. -/
private theorem p4_betaZero_pow_apply_fixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E →L[ℝ] E) (x : E) (hx : S x = x) (r : ℕ) :
    (S ^ r) x = x := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hx]

namespace GroundStatePosteriorJoint

/-- If the actual FINE coupling beta(n+1) vanishes, its entire common
right physical Krylov orbit is the unchanged normalized constant input.
No hypothesis on the distinct frozen coupling beta(n) is needed. -/
theorem fineRightFactor_eq_constantUnit_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0) :
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r =
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent (n + 1)) 2 := by
  let H := halfExtent (n + 1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
  have hFixed :
      S (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 := by
    subst_vars
    simpa only [S, hzero] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit
        H 2 specialUnitaryTwoWilsonRankPositive
  change (S ^ r) (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  exact p4_betaZero_pow_apply_fixed S _ hFixed r

/-- In particular every genuine right-Krylov member has the same
PHYSICAL input as its zero-depth member when beta(n+1)=0. -/
theorem fineRightFactor_eq_zeroDepth_of_fine_beta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hzero : beta (n + 1) = 0) :
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r =
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 := by
  rw [fineRightFactor_eq_constantUnit_of_fine_beta_zero n r hzero]
  rfl

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
