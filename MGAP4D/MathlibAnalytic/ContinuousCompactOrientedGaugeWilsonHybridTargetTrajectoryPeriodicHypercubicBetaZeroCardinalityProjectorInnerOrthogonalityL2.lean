import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanVacuumProjectorFormulaL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Distinct real eigenvalues of an inner-product symmetric continuous linear
endomorphism have orthogonal eigenvectors. -/
theorem continuousLinearMap_inner_eq_zero_of_inner_symm_eigenvectors_of_ne
    (T : V →L[ℝ] V)
    (hSymm : ∀ f g : V, inner ℝ (T f) g = inner ℝ f (T g))
    {a b : ℝ}
    {f g : V}
    (hf : T f = a • f)
    (hg : T g = b • g)
    (hab : a ≠ b) :
    inner ℝ f g = 0 := by
  have hPair := hSymm f g
  rw [hf, hg, real_inner_smul_left, real_inner_smul_right] at hPair
  have hProduct : (a - b) * inner ℝ f g = 0 := by
    rw [sub_mul]
    linarith
  exact (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr hab)

/-- Pointwise cardinality-`k` eigenaction of the actual beta-zero heat-bath
Hamiltonian. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_fluctuationCardinalityProjectorL2_eq_natCast_smul
    (k : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f) =
      (k : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f := by
  have hOperator :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_mul_fluctuationCardinalityProjectorL2_eq_natCast_smul
      k
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T f)
    hOperator
  simpa using hApply

/-- Components produced by distinct actual beta-zero cardinality projectors are
orthogonal in the Gibbs `L²` inner product. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_eq_zero_of_ne
    (k l : ℕ)
    (hkl : k ≠ l)
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          l g) = 0 := by
  have hklReal : (k : ℝ) ≠ (l : ℝ) := by
    exact_mod_cast hkl
  exact
    continuousLinearMap_inner_eq_zero_of_inner_symm_eigenvectors_of_ne
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
      (continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_fluctuationCardinalityProjectorL2_eq_natCast_smul
        k f)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_fluctuationCardinalityProjectorL2_eq_natCast_smul
        l g)
      hklReal

/-- Same-input form of pairwise cardinality-sector orthogonality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_same_input_eq_zero_of_ne
    (k l : ℕ)
    (hkl : k ≠ l)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k f)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          l f) = 0 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_eq_zero_of_ne
      k l hkl f f

/-- The vacuum component is orthogonal to every positive-cardinality component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuumComponent_fluctuationCardinalityProjectorL2_eq_zero_of_pos
    (k : ℕ)
    (hk : 0 < k)
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k g) = 0 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_eq_zero_of_ne
      0 k (Nat.ne_of_lt hk) f g

/-- Compact receipt upgrading the actual finite cardinality spectral resolution
from an algebraic direct sum to pairwise Hilbert-orthogonal components. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorInnerOrthogonalityL2Receipt :
    Prop :=
  ∀ (k l : ℕ), k ≠ l →
    ∀ f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k f)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            l g) = 0

/-- The actual beta-zero cardinality-projector inner-orthogonality receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorInnerOrthogonalityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProjectorInnerOrthogonalityL2Receipt := by
  intro k l hkl f g
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_eq_zero_of_ne
      k l hkl f g

end

end MathlibAnalytic
end MGAP4D
