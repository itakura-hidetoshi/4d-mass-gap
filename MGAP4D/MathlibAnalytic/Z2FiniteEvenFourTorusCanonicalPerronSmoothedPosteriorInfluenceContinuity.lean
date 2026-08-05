import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCanonicalPerronPosteriorEnvelopeContinuity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabSandwichFactorization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorZeroCouplingSeed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Proof-independent temporal-gauge one-slab kernel family on the complete
nonnegative coupling half-line. -/
def finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (hidden environment : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  Real.exp (-β.1 *
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
      H β.1 energyIdentity energyNontrivial hidden environment)

/-- The proof-independent family is the actual temporal-gauge Gram-kernel
entry. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (hidden environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β hidden environment =
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        H β.1 energyIdentity energyNontrivial β.2 hEnergy).kernel
        hidden environment := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
  exact
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann
      H β.1 energyIdentity energyNontrivial β.2 hEnergy
      hidden environment).symm

/-- Every proof-independent temporal-gauge kernel entry is coupling
continuous. -/
theorem continuous_finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hidden environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β hidden environment) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction
  fun_prop

/-- The raw temporal-crossing normalization scale varies continuously with
nonnegative coupling. -/
theorem continuous_finiteEvenFourTorusZ2TemporalCrossingScale
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2TemporalCrossingScale
        H β.1 energyIdentity energyNontrivial) := by
  unfold finiteEvenFourTorusZ2TemporalCrossingScale
    z2WilsonTemporalCrossingWeightSum
    z2WilsonWeightIdentity z2WilsonWeightNontrivial
  fun_prop

/-- Every fixed spatial half-weight varies continuously with coupling. -/
theorem continuous_finiteEvenFourTorusZ2SpatialHalfWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2SpatialHalfWeight
        H β.1 energyIdentity energyNontrivial A) := by
  unfold finiteEvenFourTorusZ2SpatialHalfWeight
  fun_prop

/-- Canonical hidden input weight for the Perron-smoothed posterior. -/
def finiteEvenFourTorusZ2CanonicalPerronSmoothedHiddenWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2SpatialHalfWeight
      H β.1 energyIdentity energyNontrivial hidden *
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial β hidden

/-- Canonically normalized actual Perron-smoothed hidden posterior weight. -/
def finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      H β.1 energyIdentity energyNontrivial hidden environment *
    finiteEvenFourTorusZ2CanonicalPerronSmoothedHiddenWeight
      H energyIdentity energyNontrivial β hidden

/-- Temporal-gauge raw posterior built from the continuous full kernel and the
canonical Perron ground. -/
def finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β hidden environment *
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial β hidden

/-- Pointwise coupling continuity of the temporal-gauge raw posterior. -/
theorem continuous_finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
  exact
    (continuous_finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial hidden environment).mul
    (continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_apply
      H energyIdentity energyNontrivial hEnergy hidden)

/-- Exact positive scalar relation between the raw temporal-gauge posterior and
the canonical Perron-smoothed posterior. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight_eq_scale_mul
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden =
      (finiteEvenFourTorusZ2TemporalCrossingScale
          H β.1 energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β.1 energyIdentity energyNontrivial environment) *
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
    finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
    finiteEvenFourTorusZ2CanonicalPerronSmoothedHiddenWeight
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily_eq
    H energyIdentity energyNontrivial hEnergy β hidden environment]
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
  rw [finite_os_gram_kernel_sandwich_apply]
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_scale_mul_normalized
    H β.1 energyIdentity energyNontrivial β.2 hEnergy hidden environment]
  ring

/-- The scalar relating raw and smoothed canonical posteriors is strictly
positive. -/
theorem finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorScale_pos
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2TemporalCrossingScale
          H β.1 energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β.1 energyIdentity energyNontrivial environment :=
  mul_pos
    (finiteEvenFourTorusZ2TemporalCrossingScale_pos
      H β.1 energyIdentity energyNontrivial)
    (finiteEvenFourTorusZ2SpatialHalfWeight_pos
      H β.1 energyIdentity energyNontrivial environment)

/-- Every canonical Perron-smoothed posterior weight is strictly positive,
including at zero coupling. -/
theorem finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight_pos
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
      H energyIdentity energyNontrivial β environment hidden := by
  have hRaw :
      0 < finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden := by
    unfold finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
    exact mul_pos
      (by
        unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelCouplingFamily
        exact Real.exp_pos _)
      ((finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_spec
        H energyIdentity energyNontrivial hEnergy β).2.1 hidden)
  rw [finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight_eq_scale_mul
    H energyIdentity energyNontrivial hEnergy β environment hidden] at hRaw
  rcases mul_pos_iff.mp hRaw with h | h
  · exact h.2
  · exfalso
    have hScale :=
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorScale_pos
        H energyIdentity energyNontrivial β environment
    linarith

/-- Pointwise coupling continuity of the canonical Perron-smoothed posterior
weight. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden) := by
  let scale : Set.Ici (0 : ℝ) → ℝ := fun β =>
    finiteEvenFourTorusZ2TemporalCrossingScale
        H β.1 energyIdentity energyNontrivial *
      finiteEvenFourTorusZ2SpatialHalfWeight
        H β.1 energyIdentity energyNontrivial environment
  let raw : Set.Ici (0 : ℝ) → ℝ := fun β =>
    finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
      H energyIdentity energyNontrivial β environment hidden
  have hScale : Continuous scale :=
    (continuous_finiteEvenFourTorusZ2TemporalCrossingScale
      H energyIdentity energyNontrivial).mul
    (continuous_finiteEvenFourTorusZ2SpatialHalfWeight
      H energyIdentity energyNontrivial environment)
  have hRaw : Continuous raw :=
    continuous_finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight
      H energyIdentity energyNontrivial hEnergy environment hidden
  have hScaleNe : ∀ β, scale β ≠ 0 := fun β =>
    ne_of_gt
      (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorScale_pos
        H energyIdentity energyNontrivial β environment)
  have hEq :
      (fun β : Set.Ici (0 : ℝ) =>
        finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
          H energyIdentity energyNontrivial β environment hidden) =
      fun β => (scale β)⁻¹ * raw β := by
    funext β
    have hRelation :=
      finiteEvenFourTorusZ2TemporalGaugeCanonicalRawPosteriorWeight_eq_scale_mul
        H energyIdentity energyNontrivial hEnergy β environment hidden
    change raw β = scale β *
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden at hRelation
    rw [hRelation]
    field_simp [hScaleNe β]
  rw [hEq]
  exact (hScale.inv₀ hScaleNe).mul hRaw

/-- The canonical smoothed posterior is a strictly-positive global rescaling of
the existing chosen-ground smoothed posterior. -/
theorem finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight_eq_pos_const_mul_chosen
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∃ c : ℝ,
      0 < c ∧
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
          H energyIdentity energyNontrivial β environment =
        fun hidden => c *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β.1 energyIdentity energyNontrivial β.2 hEnergy
            environment hidden := by
  obtain ⟨c, hc, hGround⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_eq_pos_smul_chosenGround
      H energyIdentity energyNontrivial hEnergy β
  refine ⟨c, hc, ?_⟩
  funext hidden
  unfold finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
    finiteEvenFourTorusZ2CanonicalPerronSmoothedHiddenWeight
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
  rw [hGround]
  change
    finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        H β.1 energyIdentity energyNontrivial hidden environment *
      (finiteEvenFourTorusZ2SpatialHalfWeight
          H β.1 energyIdentity energyNontrivial hidden *
        (c * finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β.1 energyIdentity energyNontrivial β.2 hEnergy hidden)) =
      c *
        (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β.1 energyIdentity energyNontrivial hidden environment *
          (finiteEvenFourTorusZ2SpatialHalfWeight
              H β.1 energyIdentity energyNontrivial hidden *
            finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β.1 energyIdentity energyNontrivial β.2 hEnergy hidden))
  ring

/-- Canonical influence entries are unchanged by replacing the old chosen
Perron ground by the continuous canonical representative. -/
theorem finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence_eq_chosen
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
          H energyIdentity energyNontrivial β environment)
        target source =
      finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β.1 energyIdentity energyNontrivial β.2 hEnergy environment)
        target source := by
  obtain ⟨c, hc, hWeight⟩ :=
    finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight_eq_pos_const_mul_chosen
      H energyIdentity energyNontrivial hEnergy β environment
  rw [hWeight]
  exact finitePositiveWeightCanonicalNonstrictInfluence_const_mul
    c (ne_of_gt hc)
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β.1 energyIdentity energyNontrivial β.2 hEnergy environment)
    target source

/-- Every canonical smoothed posterior influence entry is coupling continuous
on the closed nonnegative half-line. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
          H energyIdentity energyNontrivial β environment)
        target source) := by
  exact continuous_finitePositiveWeightCanonicalNonstrictInfluence
    (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
        H energyIdentity energyNontrivial β environment)
    (fun hidden =>
      continuous_finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
        H energyIdentity energyNontrivial hEnergy environment hidden)
    (fun β hidden =>
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight_pos
        H energyIdentity energyNontrivial hEnergy β environment hidden)
    target source

/-- The existing chosen-ground smoothed posterior influence has the continuous
extension supplied by the canonical representative. -/
theorem continuous_finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorInfluence
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β.1 energyIdentity energyNontrivial β.2 hEnergy environment)
        target source) := by
  have hEq :
      (fun β : Set.Ici (0 : ℝ) =>
        finitePositiveWeightCanonicalNonstrictInfluence
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β.1 energyIdentity energyNontrivial β.2 hEnergy environment)
          target source) =
      fun β =>
        finitePositiveWeightCanonicalNonstrictInfluence
          (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
            H energyIdentity energyNontrivial β environment)
          target source := by
    funext β
    exact
      (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence_eq_chosen
        H energyIdentity energyNontrivial hEnergy β environment
        target source).symm
  rw [hEq]
  exact
    continuous_finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence
      H energyIdentity energyNontrivial hEnergy environment target source

/-- The canonical representative realizes the exact zero-coupling seed. -/
@[simp] theorem finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
          H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment)
        target source = 0 := by
  rw [finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence_eq_chosen
    H energyIdentity energyNontrivial hEnergy ⟨0, by norm_num⟩
    environment target source]
  exact
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_zero_canonicalInfluence
      H energyIdentity energyNontrivial hEnergy environment target source

end

end MathlibAnalytic
end MGAP4D
