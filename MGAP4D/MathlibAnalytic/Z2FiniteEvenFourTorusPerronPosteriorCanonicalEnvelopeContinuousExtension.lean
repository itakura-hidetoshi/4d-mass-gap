import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCanonicalPerronSmoothedPosteriorInfluenceContinuity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorCanonicalEnvelopeKernel
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForContinuousEnvelope
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- Two finite nonnegative influence-kernel records are equal when their
influence functions agree. -/
theorem finiteNonnegativeInfluenceKernelData_ext_influence
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K L : FiniteNonnegativeInfluenceKernelData ι)
    (h : ∀ target source, K.influence target source = L.influence target source) :
    K = L := by
  cases K with
  | mk k hk hd =>
      cases L with
      | mk l hl ld =>
          have hkl : k = l := by
            funext target source
            exact h target source
          subst l
          rfl

/-- Closed-half-line extension of the exact environment-uniform posterior
canonical influence envelope.  The outer maximum makes nonnegativity
definitional while leaving the positive-coupling exact envelope unchanged. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if target = source then 0 else
    max 0
      (Finset.univ.sup' Finset.univ_nonempty
        (fun parameter :
            FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H =>
          finitePositiveWeightCanonicalNonstrictInfluence
            (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
              H energyIdentity energyNontrivial β
              (Function.update parameter.1.1 parameter.1.2 parameter.2))
            target source))

/-- Every entry of the closed-half-line exact envelope is coupling continuous. -/
theorem continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
        H energyIdentity energyNontrivial β target source) := by
  classical
  by_cases hEq : target = source
  · subst source
    simpa [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence]
      using (continuous_const : Continuous (fun _β : Set.Ici (0 : ℝ) => (0 : ℝ)))
  · have hSup :
        Continuous (fun β : Set.Ici (0 : ℝ) =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun parameter :
                FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H =>
              finitePositiveWeightCanonicalNonstrictInfluence
                (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
                  H energyIdentity energyNontrivial β
                  (Function.update parameter.1.1 parameter.1.2 parameter.2))
                target source)) := by
      apply Continuous.finset_sup'_apply Finset.univ_nonempty
      intro parameter _hParameter
      exact
        continuous_finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence
          H energyIdentity energyNontrivial hEnergy
          (Function.update parameter.1.1 parameter.1.2 parameter.2)
          target source
    simpa [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence,
      hEq] using (continuous_const.max hSup)

/-- The closed-half-line envelope is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
      H energyIdentity energyNontrivial β target source := by
  by_cases hEq : target = source
  · simp [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence,
      hEq]
  · rw [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence,
      if_neg hEq]
    exact le_max_left _ _

/-- The closed-half-line envelope retains zero diagonal. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_diagonal
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ))
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
      H energyIdentity energyNontrivial β target target = 0 := by
  simp [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence]

/-- The exact environment-uniform envelope starts at zero coupling with every
entry equal to zero. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ target source = 0 := by
  classical
  by_cases hEq : target = source
  · simp [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence,
      hEq]
  · simp [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence,
      hEq,
      finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence_zero
        H energyIdentity energyNontrivial hEnergy]

/-- At every strict positive coupling, the continuous extension is exactly the
existing finite maximum envelope. -/
theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_eq_existing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
        H energyIdentity energyNontrivial ⟨β, hβ.le⟩ target source =
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
        H β energyIdentity energyNontrivial hβ hEnergy target source := by
  classical
  by_cases hEq : target = source
  · subst source
    simp [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence]
  · have hSupEq :
        Finset.univ.sup' Finset.univ_nonempty
            (fun parameter :
                FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H =>
              finitePositiveWeightCanonicalNonstrictInfluence
                (finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorWeight
                  H energyIdentity energyNontrivial ⟨β, hβ.le⟩
                  (Function.update parameter.1.1 parameter.1.2 parameter.2))
                target source) =
          Finset.univ.sup' Finset.univ_nonempty
            (fun parameter :
                FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H =>
              finitePositiveWeightCanonicalNonstrictInfluence
                (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
                  H β energyIdentity energyNontrivial hβ.le hEnergy.le
                  (Function.update parameter.1.1 parameter.1.2 parameter.2))
                target source) := by
      apply congrArg
        (fun f :
            FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H → ℝ =>
          Finset.univ.sup' Finset.univ_nonempty f)
      funext parameter
      exact
        finiteEvenFourTorusZ2CanonicalPerronSmoothedPosteriorInfluence_eq_chosen
          H energyIdentity energyNontrivial hEnergy.le ⟨β, hβ.le⟩
          (Function.update parameter.1.1 parameter.1.2 parameter.2)
          target source
  have hOldSup :
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
          H β energyIdentity energyNontrivial hβ hEnergy target source =
        Finset.univ.sup' Finset.univ_nonempty
          (fun parameter :
              FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H =>
            finitePositiveWeightCanonicalNonstrictInfluence
              (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
                H β energyIdentity energyNontrivial hβ.le hEnergy.le
                (Function.update parameter.1.1 parameter.1.2 parameter.2))
              target source) := by
    rw [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence,
      if_neg hEq]
    unfold finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
    rw [Finset.max'_eq_sup', Finset.sup'_image]
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
  rw [if_neg hEq, hSupEq, ← hOldSup]
  exact max_eq_right
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy target source)

/-- Closed-half-line exact environment-uniform influence kernel. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ)) :
    FiniteNonnegativeInfluenceKernelData
      (FiniteEvenFourTorusSpatialLink H) :=
  { influence :=
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
        H energyIdentity energyNontrivial β
    influence_nonneg :=
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_nonneg
        H energyIdentity energyNontrivial β
    influence_diagonal_zero :=
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_diagonal
        H energyIdentity energyNontrivial β }

/-- The closed-half-line exact kernel agrees with the existing strict-coupling
kernel. -/
theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel_eq_existing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel
        H energyIdentity energyNontrivial ⟨β, hβ.le⟩ =
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
        H β energyIdentity energyNontrivial hβ hEnergy := by
  apply finiteNonnegativeInfluenceKernelData_ext_influence
  intro target source
  exact
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_eq_existing
      H β energyIdentity energyNontrivial hβ hEnergy target source

/-- Maximum row coefficient of the closed-half-line environment-uniform
extension. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ)) : ℝ :=
  finiteInfluenceKernelMaximumRowSum
    (finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel
      H energyIdentity energyNontrivial β)

/-- Maximum column coefficient of the closed-half-line environment-uniform
extension. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : Set.Ici (0 : ℝ)) : ℝ :=
  finiteInfluenceKernelMaximumColumnSum
    (finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel
      H energyIdentity energyNontrivial β)

/-- Coupling continuity of the exact environment-uniform maximum row
coefficient. -/
theorem continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
        H energyIdentity energyNontrivial β) := by
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
  exact continuous_finiteInfluenceKernelMaximumRowSum
    (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel
        H energyIdentity energyNontrivial β)
    (continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
      H energyIdentity energyNontrivial hEnergy)

/-- Coupling continuity of the exact environment-uniform maximum column
coefficient. -/
theorem continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Continuous (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
        H energyIdentity energyNontrivial β) := by
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
  exact continuous_finiteInfluenceKernelMaximumColumnSum
    (fun β : Set.Ici (0 : ℝ) =>
      finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel
        H energyIdentity energyNontrivial β)
    (continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence
      H energyIdentity energyNontrivial hEnergy)

/-- The environment-uniform maximum row coefficient is exactly zero at zero
coupling. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ = 0 := by
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
  rw [finiteInfluenceKernelMaximumRowSum_eq_univ_sup']
  simp [finiteInfluenceKernelRowSum,
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel,
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_zero
      H energyIdentity energyNontrivial hEnergy]

/-- The environment-uniform maximum column coefficient is exactly zero at zero
coupling. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
      H energyIdentity energyNontrivial ⟨0, by norm_num⟩ = 0 := by
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
  rw [finiteInfluenceKernelMaximumColumnSum_eq_univ_sup']
  simp [finiteInfluenceKernelColumnSum,
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel,
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeInfluence_zero
      H energyIdentity energyNontrivial hEnergy]

/-- At positive coupling the continuous maximum row coefficient is the exact
existing envelope row coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient_eq_existing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
        H energyIdentity energyNontrivial ⟨β, hβ.le⟩ =
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
  rw [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel_eq_existing
    H β energyIdentity energyNontrivial hβ hEnergy]

/-- At positive coupling the continuous maximum column coefficient is the exact
existing envelope column coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient_eq_existing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
        H energyIdentity energyNontrivial ⟨β, hβ.le⟩ =
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
  rw [finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeKernel_eq_existing
    H β energyIdentity energyNontrivial hβ hEnergy]

/-- Continuous projection of the real coupling line onto the nonnegative
half-line. -/
def finiteEvenFourTorusNonnegativeCouplingProjection
    (parameter : ℝ) : Set.Ici (0 : ℝ) :=
  ⟨max 0 parameter, le_max_left _ _⟩

/-- The nonnegative coupling projection is continuous. -/
theorem continuous_finiteEvenFourTorusNonnegativeCouplingProjection :
    Continuous finiteEvenFourTorusNonnegativeCouplingProjection := by
  unfold finiteEvenFourTorusNonnegativeCouplingProjection
  fun_prop

/-- Globally continuous real extension of the exact maximum row coefficient. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
    H energyIdentity energyNontrivial
    (finiteEvenFourTorusNonnegativeCouplingProjection parameter)

/-- Globally continuous real extension of the exact maximum column
coefficient. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
    H energyIdentity energyNontrivial
    (finiteEvenFourTorusNonnegativeCouplingProjection parameter)

/-- Global continuity of the row coefficient extension. -/
theorem continuous_finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Continuous
      (finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
        H energyIdentity energyNontrivial) := by
  unfold finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
  exact
    (continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient
      H energyIdentity energyNontrivial hEnergy).comp
        continuous_finiteEvenFourTorusNonnegativeCouplingProjection

/-- Global continuity of the column coefficient extension. -/
theorem continuous_finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Continuous
      (finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
        H energyIdentity energyNontrivial) := by
  unfold finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
  exact
    (continuous_finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient
      H energyIdentity energyNontrivial hEnergy).comp
        continuous_finiteEvenFourTorusNonnegativeCouplingProjection

/-- The real row extension starts exactly at zero. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
      H energyIdentity energyNontrivial 0 = 0 := by
  simp [finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension,
    finiteEvenFourTorusNonnegativeCouplingProjection,
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient_zero
      H energyIdentity energyNontrivial hEnergy]

/-- The real column extension starts exactly at zero. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
      H energyIdentity energyNontrivial 0 = 0 := by
  simp [finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension,
    finiteEvenFourTorusNonnegativeCouplingProjection,
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient_zero
      H energyIdentity energyNontrivial hEnergy]

/-- On every positive real coupling, the row extension is the existing exact
envelope coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension_eq_existing
    (H : ℕ)
    (parameter energyIdentity energyNontrivial : ℝ)
    (hParameter : 0 < parameter)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
        H energyIdentity energyNontrivial parameter =
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
        H parameter energyIdentity energyNontrivial hParameter hEnergy := by
  have hProjection :
      finiteEvenFourTorusNonnegativeCouplingProjection parameter =
        ⟨parameter, hParameter.le⟩ := by
    apply Subtype.ext
    simp [finiteEvenFourTorusNonnegativeCouplingProjection,
      max_eq_right hParameter.le]
  unfold finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
  rw [hProjection]
  exact
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeRowCoefficient_eq_existing
      H parameter energyIdentity energyNontrivial hParameter hEnergy

/-- On every positive real coupling, the column extension is the existing exact
envelope coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension_eq_existing
    (H : ℕ)
    (parameter energyIdentity energyNontrivial : ℝ)
    (hParameter : 0 < parameter)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
        H energyIdentity energyNontrivial parameter =
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
        H parameter energyIdentity energyNontrivial hParameter hEnergy := by
  have hProjection :
      finiteEvenFourTorusNonnegativeCouplingProjection parameter =
        ⟨parameter, hParameter.le⟩ := by
    apply Subtype.ext
    simp [finiteEvenFourTorusNonnegativeCouplingProjection,
      max_eq_right hParameter.le]
  unfold finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
  rw [hProjection]
  exact
    finiteEvenFourTorusZ2PerronPosteriorContinuousEnvelopeColumnCoefficient_eq_existing
      H parameter energyIdentity energyNontrivial hParameter hEnergy

end

end MathlibAnalytic
end MGAP4D
