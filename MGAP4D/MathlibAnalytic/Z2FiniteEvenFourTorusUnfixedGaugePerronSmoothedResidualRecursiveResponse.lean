import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltStationaryResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSandwichLocalCrossRatioRows
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Unnormalized hidden posterior weight at one observed spatial environment
for the Perron smoothed residual. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      H β energyIdentity energyNontrivial hidden environment *
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
      H β energyIdentity energyNontrivial hβ hEnergy hidden

/-- Every hidden posterior weight is strictly positive at strict coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      environment hidden := by
  exact mul_pos
    (by
      unfold finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      exact finiteZ2GaugeNormalizedProductKernel_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
        (FiniteEvenFourTorusSpatialLink H) hidden environment)
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight_pos
      H β energyIdentity energyNontrivial hβ.le hEnergy.le hidden)

/-- The generic kernel tilt expectation is exactly the normalized global
expectation for the corresponding hidden posterior weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (base environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
        H β energyIdentity energyNontrivial hβ hEnergy
        base environment source replacement =
      finitePositiveWeightGlobalExpectation
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy environment)
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
          H β energyIdentity energyNontrivial base source replacement) := by
  classical
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
    finitePositiveKernelTiltExpectation finitePositiveKernelPosterior
    finitePositiveWeightGlobalExpectation
    finitePositiveWeightGlobalProbability
    finitePositiveWeightTotalMass
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    finitePositiveKernelNormalizer
  rfl

/-- Target-coordinate reweighting of the hidden posterior produced by changing
one observed target value. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge) :
    FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
  finiteZ2GaugeNormalizedProductKernelBoundaryTilt
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
    base target replacement

/-- The target reweighting tilt is supported exactly on the hidden target
coordinate. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_supportedOn_target
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge) :
    FiniteProductFunctionSupportedOn ({target} :
      Finset (FiniteEvenFourTorusSpatialLink H))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
        H β energyIdentity energyNontrivial base target replacement) := by
  exact finiteZ2GaugeNormalizedProductKernelBoundaryTilt_supportedOn_source
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
    base target replacement

/-- The target reweighting tilt is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
      H β energyIdentity energyNontrivial base target replacement hidden := by
  exact finiteZ2GaugeNormalizedProductKernelBoundaryTilt_pos
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    base target replacement hidden

/-- Uniform upper likelihood-ratio bound for the target reweighting tilt. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_le_ratio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
        H β energyIdentity energyNontrivial base target replacement hidden ≤
      finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) := by
  let q := z2WilsonTemporalCrossingRate
    β energyIdentity energyNontrivial
  let oldLocal := finiteZ2NormalizedLocalKernel q
    (boolEquivZ2Gauge.symm (hidden target))
    (boolEquivZ2Gauge.symm (base target))
  let newLocal := finiteZ2NormalizedLocalKernel q
    (boolEquivZ2Gauge.symm (hidden target))
    (boolEquivZ2Gauge.symm replacement)
  have hOld : 0 < oldLocal :=
    finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy) _ _
  have hRatio := finiteZ2NormalizedLocalKernel_le_likelihoodRatio_mul
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    (boolEquivZ2Gauge.symm (hidden target))
    (boolEquivZ2Gauge.symm replacement)
    (boolEquivZ2Gauge.symm (base target))
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
    finiteZ2GaugeNormalizedProductKernelBoundaryTilt
  change newLocal / oldLocal ≤ finiteZ2CrossingLikelihoodRatio q
  exact (div_le_iff₀ hOld).2 (by simpa [mul_comm] using hRatio)

/-- Uniform inverse-ratio lower bound for the target reweighting tilt. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial))⁻¹ ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
        H β energyIdentity energyNontrivial base target replacement hidden := by
  let q := z2WilsonTemporalCrossingRate
    β energyIdentity energyNontrivial
  let R := finiteZ2CrossingLikelihoodRatio q
  let oldLocal := finiteZ2NormalizedLocalKernel q
    (boolEquivZ2Gauge.symm (hidden target))
    (boolEquivZ2Gauge.symm (base target))
  let newLocal := finiteZ2NormalizedLocalKernel q
    (boolEquivZ2Gauge.symm (hidden target))
    (boolEquivZ2Gauge.symm replacement)
  have hOld : 0 < oldLocal :=
    finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy) _ _
  have hR : 0 < R := finiteZ2CrossingLikelihoodRatio_pos
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  have hReverse := finiteZ2NormalizedLocalKernel_le_likelihoodRatio_mul
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    (boolEquivZ2Gauge.symm (hidden target))
    (boolEquivZ2Gauge.symm (base target))
    (boolEquivZ2Gauge.symm replacement)
  have hScaled : R⁻¹ * oldLocal ≤ newLocal := by
    calc
      R⁻¹ * oldLocal ≤ R⁻¹ * (R * newLocal) :=
        mul_le_mul_of_nonneg_left hReverse (le_of_lt (inv_pos.mpr hR))
      _ = newLocal := by field_simp [ne_of_gt hR]
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
    finiteZ2GaugeNormalizedProductKernelBoundaryTilt
  change R⁻¹ ≤ newLocal / oldLocal
  exact (le_div_iff₀ hOld).2 hScaled

/-- Exact hidden posterior reweighting identity between two target values. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_update_target_eq_tilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update environment target h) =
      finitePositiveWeightMultiplicativeTilt
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (Function.update environment target g))
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
          H β energyIdentity energyNontrivial
          (Function.update environment target g) target h) := by
  funext hidden
  have hRelation :=
    finiteZ2GaugeNormalizedProductKernel_boundaryTiltRelation
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
      (FiniteEvenFourTorusSpatialLink H)
      (Function.update environment target g) target h hidden
  have hReplace :
      finiteZ2GaugeReplaceCoordinate
          (Function.update environment target g) target h =
        Function.update environment target h := by
    funext coordinate
    by_cases hCoordinate : coordinate = target
    · subst coordinate
      simp [finiteZ2GaugeReplaceCoordinate]
    · simp [finiteZ2GaugeReplaceCoordinate, Function.update, hCoordinate]
  rw [hReplace] at hRelation
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    finitePositiveWeightMultiplicativeTilt
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
    finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel at *
  rw [hRelation]
  ring

/-- Singleton variation profile for a source-local residual boundary tilt. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (coordinate : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if coordinate = source then
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) -
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
  else 0

/-- The singleton source-tilt variation profile is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (source coordinate : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation
      H β energyIdentity energyNontrivial source coordinate := by
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation
  split
  · have hR1 := one_le_finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    have hRpos := finiteZ2CrossingLikelihoodRatio_pos
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    have hInv :
        (finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial))⁻¹ ≤ 1 := by
      exact (inv_le_one₀ hRpos).2 hR1
    linarith
  · exact le_rfl

/-- The source-local crossing tilt has the explicit singleton variation bound
`R - R⁻¹`. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariationBound
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge) :
    FiniteProductVariationBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
        H β energyIdentity energyNontrivial base source replacement) :=
  { variation :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation
        H β energyIdentity energyNontrivial source
    variation_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy source
    variation_bound := by
      intro coordinate A B hAgree
      by_cases hCoordinate : coordinate = source
      · subst coordinate
        have hLowerA :=
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
            H β energyIdentity energyNontrivial hβ hEnergy
            base source replacement A
        have hUpperA :=
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_le_ratio
            H β energyIdentity energyNontrivial hβ hEnergy
            base source replacement A
        have hLowerB :=
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
            H β energyIdentity energyNontrivial hβ hEnergy
            base source replacement B
        have hUpperB :=
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_le_ratio
            H β energyIdentity energyNontrivial hβ hEnergy
            base source replacement B
        unfold
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt at hLowerA hUpperA hLowerB hUpperB ⊢
        rw [finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation]
        simp only [if_pos rfl]
        rw [abs_le]
        constructor <;> linarith
      · have hEq :
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
              H β energyIdentity energyNontrivial base source replacement A =
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
              H β energyIdentity energyNontrivial base source replacement B := by
          apply
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt_supportedOn_source
              H β energyIdentity energyNontrivial base source replacement
          intro link hLink
          simp only [Finset.mem_singleton] at hLink
          subst link
          exact hAgree source (Ne.symm hCoordinate)
        rw [hEq, sub_self, abs_zero]
        exact
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation_nonneg
            H β energyIdentity energyNontrivial hβ hEnergy source source
  }

/-- Total mass of the singleton source-tilt variation profile. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation_total
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H) :
    finiteProductVariationTotal
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation
          H β energyIdentity energyNontrivial source) =
      finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) -
        (finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial))⁻¹ := by
  classical
  unfold finiteProductVariationTotal
  rw [Finset.sum_eq_single source]
  · simp [finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation]
  · intro coordinate _hCoordinate hCoordinateSource
    simp [finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation,
      hCoordinateSource]
  · intro hSource
    exact False.elim (hSource (Finset.mem_univ source))

/-- Recursive finite-step response error for one source-local residual tilt
under a target-local change of the observed boundary. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResponseError
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (g h replacement : Z2Gauge)
    (D : FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update environment target g)))
    (n : ℕ) : ℝ :=
  let rightWeight :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      (Function.update environment target g)
  let targetTilt :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
      H β energyIdentity energyNontrivial
      (Function.update environment target g) target h
  let P :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariationBound
      H β energyIdentity energyNontrivial hβ hEnergy
      environment source replacement
  let R := finiteZ2CrossingLikelihoodRatio
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
  let hRpos : 0 < R := finiteZ2CrossingLikelihoodRatio_pos
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  let hRone : 1 ≤ R := one_le_finiteZ2CrossingLikelihoodRatio
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  let C :=
    finitePositiveWeightLocalTiltStationaryComparisonData
      rightWeight targetTilt
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g) target h)
      ({target} : Finset (FiniteEvenFourTorusSpatialLink H))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_supportedOn_target
        H β energyIdentity energyNontrivial
        (Function.update environment target g) target h)
      R⁻¹ R
      (inv_pos.mpr hRpos)
      hRpos
      (le_trans ((inv_le_one₀ hRpos).2 hRone) hRone)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g) target h)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_le_ratio
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g) target h)
      (Fintype.card_pos_iff.mpr ⟨target⟩) D
  FinitePositiveWeightStationaryRandomScanComparisonData.partialStationarySource
      P C n +
    2 * finitePositiveWeightDobrushinRandomScanRate D ^ n *
      finiteProductVariationTotal P.variation

/-- The recursive response error controls the difference of source-tilt
expectations between two target values. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_difference_abs_le_recursiveResponse
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (g h replacement : Z2Gauge)
    (D : FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update environment target g)))
    (n : ℕ) :
    |finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          environment (Function.update environment target h)
          source replacement -
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          environment (Function.update environment target g)
          source replacement| ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResponseError
        H β energyIdentity energyNontrivial hβ hEnergy
        environment target source g h replacement D n := by
  let R := finiteZ2CrossingLikelihoodRatio
    (z2WilsonTemporalCrossingRate β energyIdentity energyNontrivial)
  have hRpos : 0 < R := finiteZ2CrossingLikelihoodRatio_pos
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  have hRone : 1 ≤ R := one_le_finiteZ2CrossingLikelihoodRatio
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_update_target_eq_tilt
      H β energyIdentity energyNontrivial hβ hEnergy environment target g h]
  exact
    finitePositiveWeightLocalTilt_globalExpectation_discrepancy_le
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update environment target g))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt
        H β energyIdentity energyNontrivial
        (Function.update environment target g) target h)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g) target h)
      ({target} : Finset (FiniteEvenFourTorusSpatialLink H))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_supportedOn_target
        H β energyIdentity energyNontrivial
        (Function.update environment target g) target h)
      R⁻¹ R
      (inv_pos.mpr hRpos)
      hRpos
      (le_trans ((inv_le_one₀ hRpos).2 hRone) hRone)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g) target h)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_le_ratio
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update environment target g) target h)
      (Fintype.card_pos_iff.mpr ⟨target⟩)
      D
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariationBound
        H β energyIdentity energyNontrivial hβ hEnergy
        environment source replacement)
      n

/-- A uniform bound on the recursive target-response errors gives the exact
smoothed-residual four-point cross-ratio. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_recursiveResponse
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (n : ℕ)
    (errorBound : ℝ)
    (hErrorNonneg : 0 ≤ errorBound)
    (D : ∀ g : Z2Gauge,
      FinitePositiveWeightDobrushinL1MatrixData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (Function.update A target g)))
    (hError :
      ∀ g h : Z2Gauge,
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResponseError
          H β energyIdentity energyNontrivial hβ hEnergy
          A target source g h (C source) (D g) n ≤ errorBound) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      A C target
      (1 + finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) * errorBound) := by
  apply
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_sourceTiltExpectation
      H β energyIdentity energyNontrivial hβ hEnergy
      A C target source hNe hAgree
  intro g h
  let rightWeight :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      (Function.update A target g)
  let sourceTilt :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
      H β energyIdentity energyNontrivial A source (C source)
  have hDiscrepancy :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_difference_abs_le_recursiveResponse
      H β energyIdentity energyNontrivial hβ hEnergy
      A target source g h (C source) (D g) n
  have hDiscrepancyBound :
      |finitePositiveWeightGlobalExpectation
            (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
              H β energyIdentity energyNontrivial hβ.le hEnergy.le
              (Function.update A target h)) sourceTilt -
          finitePositiveWeightGlobalExpectation rightWeight sourceTilt| ≤
        errorBound := by
    rw [←
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation,
      ←
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation]
    exact hDiscrepancy.trans (hError g h)
  have hOneSided :=
    finitePositiveWeightGlobalExpectation_le_one_add_error_div_lower_mul
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update A target h))
      rightWeight
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update A target g))
      sourceTilt
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
      errorBound
      (inv_pos.mpr (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
        H β energyIdentity energyNontrivial hβ hEnergy
        A source (C source))
      hErrorNonneg hDiscrepancyBound
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation]
  simpa [rightWeight, sourceTilt, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hOneSided

end

end MathlibAnalytic
end MGAP4D
