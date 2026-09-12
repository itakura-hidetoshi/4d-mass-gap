import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalScaleZeroInfluence
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedResidualRecursiveResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalCrossingRawNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- At zero coupling the exact temporal crossing sign-mode rate vanishes. -/
@[simp] theorem z2WilsonTemporalCrossingRate_zero
    (energyIdentity energyNontrivial : ℝ) :
    z2WilsonTemporalCrossingRate
      0 energyIdentity energyNontrivial = 0 := by
  simp [z2WilsonTemporalCrossingRate,
    z2WilsonTemporalCrossingWeightSum,
    z2WilsonWeightIdentity, z2WilsonWeightNontrivial]

/-- Every spatial half-weight is exactly one at zero coupling. -/
@[simp] theorem finiteEvenFourTorusZ2SpatialHalfWeight_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialHalfWeight
      H 0 energyIdentity energyNontrivial A = 1 := by
  simp [finiteEvenFourTorusZ2SpatialHalfWeight]

/-- The exact unfixed-gauge one-slab kernel is the constant-one kernel at zero
coupling.  The normalized temporal-link sum contributes no residual scalar. -/
@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H 0 energyIdentity energyNontrivial (by norm_num) hEnergy A B = 1 := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  have hcardNat :
      0 < Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcardReal :
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcardNat)
  simp [hcardReal]

/-- At zero coupling the normalized unfixed-gauge transfer sends every vector
to a configuration-independent vector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_zero_apply_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy f A =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy f B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
    finiteKernelNormalizedOperator
  simp only [ContinuousLinearMap.smul_apply]
  change
    ‖finiteKernelOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy)‖⁻¹ *
        (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H 0 energyIdentity energyNontrivial (by norm_num) hEnergy x A *
            f x) =
      ‖finiteKernelOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy)‖⁻¹ *
        (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H 0 energyIdentity energyNontrivial (by norm_num) hEnergy x B *
            f x)
  simp

/-- The existing chosen Perron ground is necessarily constant on the complete
finite boundary carrier at zero coupling.  This conclusion is independent of
its noncanonical scale. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_zero_apply_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy A =
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy B := by
  let ground :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
  have hfixed :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
      H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
  have hA := congrArg
    (fun f : FiniteEvenFourTorusZ2SliceHilbert H => f A) hfixed
  have hB := congrArg
    (fun f : FiniteEvenFourTorusZ2SliceHilbert H => f B) hfixed
  change
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy ground A =
      ground A at hA
  change
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy ground B =
      ground B at hB
  calc
    ground A =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy ground A :=
      hA.symm
    _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy ground B :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_zero_apply_eq
        H energyIdentity energyNontrivial hEnergy ground A B
    _ = ground B := hB

/-- At zero coupling the normalized temporal crossing kernel does not depend on
the hidden boundary configuration. -/
theorem finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel_zero_hidden_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hidden₁ hidden₂ environment :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        H 0 energyIdentity energyNontrivial hidden₁ environment =
      finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        H 0 energyIdentity energyNontrivial hidden₂ environment := by
  unfold finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
  rw [z2WilsonTemporalCrossingRate_zero]
  rw [finiteZ2GaugeNormalizedProductKernel_apply,
    finiteZ2GaugeNormalizedProductKernel_apply]
  apply Finset.prod_congr rfl
  intro e _he
  simp [finiteZ2NormalizedLocalKernel]

/-- The Perron-smoothed hidden input weight is configuration-independent at
zero coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight_zero_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hidden₁ hidden₂ : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy hidden₁ =
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy hidden₂ := by
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
  rw [finiteEvenFourTorusZ2SpatialHalfWeight_zero,
    finiteEvenFourTorusZ2SpatialHalfWeight_zero,
    one_mul, one_mul]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_zero_apply_eq
      H energyIdentity energyNontrivial hEnergy hidden₁ hidden₂

/-- For every observed environment, the actual hidden posterior weight is
configuration-independent at zero coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_zero_hidden_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden₁ hidden₂ :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
        environment hidden₁ =
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
        environment hidden₂ := by
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
  rw [finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel_zero_hidden_eq
      H energyIdentity energyNontrivial hidden₁ hidden₂ environment,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight_zero_eq
      H energyIdentity energyNontrivial hEnergy hidden₁ hidden₂]

/-- The actual zero-coupling posterior has exact zero one-source conditional
`L¹` response for every environment and every ordered coordinate pair. -/
@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_zero_conditionalL1
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finitePositiveWeightSingleSiteConditionalL1
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy environment)
      A B target = 0 := by
  let hidden₀ : FiniteEvenFourTorusZ2SliceConfiguration H := fun _ => 1
  let c :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
      environment hidden₀
  have hWeight :
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy environment =
        fun _hidden => c := by
    funext hidden
    exact
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_zero_hidden_eq
        H energyIdentity energyNontrivial hEnergy environment hidden hidden₀
  rw [hWeight]
  exact finitePositiveWeightSingleSiteConditionalL1_of_const c A B target

/-- Actual realization of the zero-coupling strict seed: every canonical
non-strict posterior influence entry is exactly zero, without any continuity
assumption. -/
@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_zero_canonicalInfluence
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finitePositiveWeightCanonicalNonstrictInfluence
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy environment)
      target source = 0 := by
  let hidden₀ : FiniteEvenFourTorusZ2SliceConfiguration H := fun _ => 1
  let c :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
      environment hidden₀
  have hWeight :
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy environment =
        fun _hidden => c := by
    funext hidden
    exact
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_zero_hidden_eq
        H energyIdentity energyNontrivial hEnergy environment hidden hidden₀
  rw [hWeight]
  exact finitePositiveWeightCanonicalNonstrictInfluence_of_const
    c target source

end

end MathlibAnalytic
end MGAP4D
