import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonKernelTopologicalDecompositionL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The four Moore--Penrose equations for a pair of continuous linear
endomorphisms of a real Hilbert space.  The final two conditions are expressed
through the real inner product rather than a bundled adjoint. -/
structure ContinuousLinearMapMoorePenrosePair
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G : E →L[ℝ] E) : Prop where
  apply_inverse_apply :
    A.comp (G.comp A) = A
  inverse_apply_inverse :
    G.comp (A.comp G) = G
  apply_inverse_inner_symm :
    ∀ f g : E,
      inner ℝ (A (G f)) g = inner ℝ f (A (G g))
  inverse_apply_inner_symm :
    ∀ f g : E,
      inner ℝ (G (A f)) g = inner ℝ f (G (A g))

/-- Subtracting the rank-one map `f ↦ ⟪omega, f⟫ omega` is inner symmetric on
any real inner-product space. -/
theorem inner_sub_inner_smul_self_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (omega f g : E) :
    inner ℝ (f - inner ℝ omega f • omega) g =
      inner ℝ f (g - inner ℝ omega g • omega) := by
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm f omega]
  ring

/-- Ambient orthogonal centering away from the normalized Gibbs vacuum. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  ContinuousLinearMap.id ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0

/-- Pointwise form of ambient centering. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  rfl

/-- Ambient centering is the orthogonal projection onto `Ω⊥`, hence it is
inner symmetric. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_inner_symm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 g) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum]
  exact inner_sub_inner_smul_self_symm
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f g

/-- Operator-level form of `(I-P) G† = C`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_comp_generalizedInverse_eq_centeringEndL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]

/-- Operator-level form of `G† (I-P) = C`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_comp_poisson_eq_centeringEndL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]

/-- The Poisson operator and its generalized inverse commute, with common
product equal to orthogonal centering. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_comp_generalizedInverse_eq_generalizedInverse_comp_poisson :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_comp_generalizedInverse_eq_centeringEndL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_comp_poisson_eq_centeringEndL2]

/-- Operator-level first Penrose equation `A G† A = A`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_comp_generalizedInverse_comp_poisson_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.comp
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 := by
  apply ContinuousLinearMap.ext
  intro f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_apply_poisson_eq_self
      f

/-- Operator-level second Penrose equation `G† A G† = G†`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_comp_poisson_comp_generalizedInverse_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.comp
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 := by
  apply ContinuousLinearMap.ext
  intro f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_apply_generalizedInverse_eq_self
      f

/-- The product `A G†` is inner symmetric. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_inner_symm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f))
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            g)) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector]
  simpa only [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_inner_symm
      f g

/-- The product `G† A` is inner symmetric. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_inner_symm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f))
        g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            g)) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector]
  simpa only [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_inner_symm
      f g

/-- The ambient generalized inverse satisfies all four Moore--Penrose
equations for the actual beta-zero Poisson operator. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isMoorePenrose :
    ContinuousLinearMapMoorePenrosePair
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 := by
  refine
    { apply_inverse_apply :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_comp_generalizedInverse_comp_poisson_eq_self
      inverse_apply_inverse :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_comp_poisson_comp_generalizedInverse_eq_self
      apply_inverse_inner_symm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_inner_symm
      inverse_apply_inner_symm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_inner_symm }

/-- The generalized inverse and the Poisson operator have the same kernel. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_ker_eq_poisson_ker :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.toLinearMap.ker =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.ker := by
  ext f
  constructor
  · intro hf
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f = 0 at hf
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f = 0
    have hCenter :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector
        f
    rw [hf, map_zero] at hCenter
    have hVacuum :
        f =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f :=
      sub_eq_zero.mp hCenter.symm
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
        f).2 hVacuum
  · intro hf
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f = 0 at hf
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f = 0
    have hCenter :
        f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f = 0 := by
      have hGA :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector
          f
      rw [hf, map_zero] at hGA
      exact hGA.symm
    have hAGZero :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f) = 0 := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
        hCenter]
    have hPenrose :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_apply_generalizedInverse_eq_self
        f
    rw [hAGZero, map_zero] at hPenrose
    exact hPenrose.symm

/-- The generalized inverse has exactly the vacuum-orthogonal range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_range_eq_vacuumOrthogonalSubmoduleL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.toLinearMap.range =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        g
  · intro hf
    let fOrthogonal :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
      ⟨f, hf⟩
    refine
      ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 f,
        ?_⟩
    have hPoisson :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_centering
        f
    have hCentering :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_subtype_eq_self
        fOrthogonal
    have hCenteringCoe := congrArg
      (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (z : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hCentering
    exact hPoisson.trans hCenteringCoe

/-- The generalized inverse and the Poisson operator have the same range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_range_eq_poisson_range :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.toLinearMap.range =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_range_eq_vacuumOrthogonalSubmoduleL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_range_eq_vacuumOrthogonalSubmoduleL2]

/-- Structured receipt for the exact beta-zero Moore--Penrose geometry. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenroseL2Receipt :
    Prop where
  moore_penrose :
    ContinuousLinearMapMoorePenrosePair
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
  common_product :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
  ker_eq :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.toLinearMap.ker =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.ker
  range_eq :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.toLinearMap.range =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range
  range_eq_vacuumOrthogonal :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.toLinearMap.range =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
  norm_eq_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2‖ =
      324

/-- The exact beta-zero Moore--Penrose receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenroseL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenroseL2Receipt := by
  refine
    { moore_penrose :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_isMoorePenrose
      common_product :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_comp_generalizedInverse_eq_centeringEndL2
      ker_eq :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_ker_eq_poisson_ker
      range_eq :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_range_eq_poisson_range
      range_eq_vacuumOrthogonal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_range_eq_vacuumOrthogonalSubmoduleL2
      norm_eq_324 :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_eq_324 }

end

end MathlibAnalytic
end MGAP4D
