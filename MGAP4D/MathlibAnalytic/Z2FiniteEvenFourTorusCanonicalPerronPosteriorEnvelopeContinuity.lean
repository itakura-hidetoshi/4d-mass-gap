import MGAP4D.MathlibAnalytic.FiniteContinuousPositiveWeightCanonicalInfluence
import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalScaleZeroInfluence
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorZeroCouplingSeed
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeCanonicalPerronGroundContinuity
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Proof-independent actual posterior weight obtained directly from the full
one-slab kernel and the continuously normalized Perron ground. -/
def finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β.1 hidden environment *
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial β hidden

/-- Every direct canonical posterior weight is strictly positive. -/
theorem finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight_pos
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
      H energyIdentity energyNontrivial β environment hidden := by
  unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
  exact mul_pos
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_pos
      H energyIdentity energyNontrivial β.1 hidden environment)
    ((finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_spec
      H energyIdentity energyNontrivial hEnergy β).2.1 hidden)

/-- Every coordinate of the canonical Perron ground varies continuously with
nonnegative coupling. -/
theorem continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_apply
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial β hidden) := by
  let E :=
    PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : FiniteEvenFourTorusZ2SliceConfiguration H => ℝ)
  have hGround :=
    continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial hEnergy
  have hPlain : Continuous (fun β : Set.Ici (0 : ℝ) =>
      E (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial β)) :=
    E.continuous.comp hGround
  have hCoordinate : Continuous (fun β : Set.Ici (0 : ℝ) =>
      E (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial β) hidden) :=
    (continuous_apply hidden).comp hPlain
  simpa [E] using hCoordinate

/-- Pointwise coupling continuity of the direct actual canonical posterior
weight. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
        H energyIdentity energyNontrivial β environment hidden) := by
  unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
  exact
    ((continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial hidden environment).comp
        continuous_subtype_val).mul
      (continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_apply
        H energyIdentity energyNontrivial hEnergy hidden)

/-- Canonical non-strict actual posterior influence kernel at one coupling and
one observed environment. -/
noncomputable def finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteNonnegativeInfluenceKernelData
      (FiniteEvenFourTorusSpatialLink H) :=
  { influence := fun target source =>
      finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
          H energyIdentity energyNontrivial β environment)
        target source
    influence_nonneg := by
      intro target source
      exact finitePositiveWeightCanonicalNonstrictInfluence_nonneg
        (finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
          H energyIdentity energyNontrivial β environment)
        target source
    influence_diagonal_zero := by
      intro e
      exact finitePositiveWeightCanonicalNonstrictInfluence_diagonal
        (finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
          H energyIdentity energyNontrivial β environment) e }

/-- Every entry of the actual canonical posterior influence kernel varies
continuously with nonnegative coupling. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluence
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      (finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
        H energyIdentity energyNontrivial β environment).influence
          target source) := by
  exact continuous_finitePositiveWeightCanonicalNonstrictInfluence
    (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
        H energyIdentity energyNontrivial β environment)
    (fun hidden =>
      continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
        H energyIdentity energyNontrivial hEnergy environment hidden)
    (fun β hidden =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight_pos
        H energyIdentity energyNontrivial hEnergy β environment hidden)
    target source

/-- Maximum row coefficient of the actual canonical posterior influence
kernel. -/
noncomputable def finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteInfluenceKernelMaximumRowSum
    (finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
      H energyIdentity energyNontrivial β environment)

/-- Maximum column coefficient of the actual canonical posterior influence
kernel. -/
noncomputable def finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteInfluenceKernelMaximumColumnSum
    (finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
      H energyIdentity energyNontrivial β environment)

/-- Finite row/column envelope coefficient of the actual canonical posterior. -/
noncomputable def finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  max
    (finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
      H energyIdentity energyNontrivial β environment)
    (finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
      H energyIdentity energyNontrivial β environment)

/-- Coupling continuity of the exact maximum row coefficient. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
        H energyIdentity energyNontrivial β environment) := by
  unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
  exact continuous_finiteInfluenceKernelMaximumRowSum
    (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
        H energyIdentity energyNontrivial β environment)
    (continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluence
      H energyIdentity energyNontrivial hEnergy environment)

/-- Coupling continuity of the exact maximum column coefficient. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
        H energyIdentity energyNontrivial β environment) := by
  unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
  exact continuous_finiteInfluenceKernelMaximumColumnSum
    (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
        H energyIdentity energyNontrivial β environment)
    (continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluence
      H energyIdentity energyNontrivial hEnergy environment)

/-- Coupling continuity of the combined actual finite row/column envelope. -/
theorem continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope
        H energyIdentity energyNontrivial β environment) := by
  unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope
  exact
    (continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
      H energyIdentity energyNontrivial hEnergy environment).max
    (continuous_finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
      H energyIdentity energyNontrivial hEnergy environment)

/-- At zero coupling the canonical Perron ground is independent of the slice
configuration. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩ A =
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩ B := by
  obtain ⟨c, _hcPos, hc⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_eq_pos_smul_chosenGround
      H energyIdentity energyNontrivial hEnergy ⟨0, by norm_num⟩
  rw [hc]
  change c *
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy A =
    c * finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy B
  rw [finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_zero_apply_eq
    H energyIdentity energyNontrivial hEnergy A B]

/-- At zero coupling the direct canonical posterior weight is independent of
the hidden slice. -/
theorem finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight_zero_hidden_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden₁ hidden₂ :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩
        environment hidden₁ =
      finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩
        environment hidden₂ := by
  unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
  change
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
        hidden₁ environment *
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩ hidden₁ =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H 0 energyIdentity energyNontrivial (by norm_num) hEnergy
        hidden₂ environment *
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩ hidden₂
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_zero,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_zero,
    one_mul, one_mul]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply_eq
      H energyIdentity energyNontrivial hEnergy hidden₁ hidden₂

/-- Every actual canonical posterior influence entry is exactly zero at zero
coupling. -/
@[simp] theorem finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluence_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    (finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluenceKernel
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment).influence
        target source = 0 := by
  let hidden₀ : FiniteEvenFourTorusZ2SliceConfiguration H := fun _ => 1
  let c :=
    finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment hidden₀
  have hWeight :
      finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
          H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment =
        fun _hidden => c := by
    funext hidden
    exact finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight_zero_hidden_eq
      H energyIdentity energyNontrivial hEnergy environment hidden hidden₀
  change
    finitePositiveWeightCanonicalNonstrictInfluence
      (finiteEvenFourTorusZ2CanonicalPerronPosteriorWeight
        H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment)
      target source = 0
  rw [hWeight]
  exact finitePositiveWeightCanonicalNonstrictInfluence_of_const
    c target source

/-- The maximum row coefficient is exactly zero at zero coupling. -/
@[simp] theorem finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment = 0 := by
  apply le_antisymm
  · unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow
    apply finiteInfluenceKernelMaximumRowSum_le_of_forall
    intro target
    unfold finiteInfluenceKernelRowSum
    simp [finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluence_zero
      H energyIdentity energyNontrivial hEnergy environment]
  · exact finiteInfluenceKernelMaximumRowSum_nonneg _

/-- The maximum column coefficient is exactly zero at zero coupling. -/
@[simp] theorem finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment = 0 := by
  apply le_antisymm
  · unfold finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn
    apply finiteInfluenceKernelMaximumColumnSum_le_of_forall
    intro source
    unfold finiteInfluenceKernelColumnSum
    simp [finiteEvenFourTorusZ2CanonicalPerronPosteriorInfluence_zero
      H energyIdentity energyNontrivial hEnergy environment]
  · exact finiteInfluenceKernelMaximumColumnSum_nonneg _

/-- The combined actual posterior envelope is exactly zero at zero coupling. -/
@[simp] theorem finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ environment = 0 := by
  simp [finiteEvenFourTorusZ2CanonicalPerronPosteriorEnvelope,
    finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumRow_zero
      H energyIdentity energyNontrivial hEnergy environment,
    finiteEvenFourTorusZ2CanonicalPerronPosteriorMaximumColumn_zero
      H energyIdentity energyNontrivial hEnergy environment]

end

end MathlibAnalytic
end MGAP4D
