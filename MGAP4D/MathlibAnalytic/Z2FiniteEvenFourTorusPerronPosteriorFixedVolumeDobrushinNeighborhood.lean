import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorCanonicalEnvelopeContinuousExtension
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A real continuous scalar function that vanishes at zero is strictly below
`1/2` on some two-sided neighborhood of zero.  This elementary metric lemma is
kept generic so the posterior row and column coefficients share one proof. -/
theorem continuous_zero_exists_abs_lt_half
    (f : ℝ → ℝ)
    (hf : Continuous f)
    (h0 : f 0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x < (1 / 2 : ℝ) := by
  have hMetric :=
    (Metric.continuousAt_iff.mp hf.continuousAt) (1 / 2 : ℝ) (by norm_num)
  obtain ⟨ε, hε, hControl⟩ := hMetric
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hdist : dist x 0 < ε := by
    simpa [Real.dist_eq] using hx
  have hout := hControl x hdist
  rw [h0] at hout
  have habs : |f x| < (1 / 2 : ℝ) := by
    simpa [Real.dist_eq] using hout
  exact lt_of_le_of_lt (le_abs_self (f x)) habs

/-- For every fixed finite side parameter, the exact environment-uniform
Perron-posterior row and column coefficients are simultaneously below `1/2`
on a sufficiently small positive-coupling interval.

The radius may depend on `H`; this theorem is therefore a fixed-volume
Dobrushin neighborhood, not yet the volume-uniform mass-gap estimate. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelope_exists_smallPositive_row_column_lt_half
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
              H β energyIdentity energyNontrivial hβ hEnergy < (1 / 2 : ℝ) ∧
          finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
              H β energyIdentity energyNontrivial hβ hEnergy < (1 / 2 : ℝ) := by
  let row :=
    finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
      H energyIdentity energyNontrivial
  let column :=
    finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
      H energyIdentity energyNontrivial
  have hRowContinuous : Continuous row := by
    simpa [row] using
      continuous_finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
        H energyIdentity energyNontrivial hEnergy.le
  have hColumnContinuous : Continuous column := by
    simpa [column] using
      continuous_finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
        H energyIdentity energyNontrivial hEnergy.le
  have hRowZero : row 0 = 0 := by
    simpa [row] using
      finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension_zero
        H energyIdentity energyNontrivial hEnergy.le
  have hColumnZero : column 0 = 0 := by
    simpa [column] using
      finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension_zero
        H energyIdentity energyNontrivial hEnergy.le
  obtain ⟨εRow, hεRow, hRow⟩ :=
    continuous_zero_exists_abs_lt_half row hRowContinuous hRowZero
  obtain ⟨εColumn, hεColumn, hColumn⟩ :=
    continuous_zero_exists_abs_lt_half column hColumnContinuous hColumnZero
  let ε := min εRow εColumn
  have hε : 0 < ε := lt_min hεRow hεColumn
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  have hβRow : β < εRow := lt_of_lt_of_le hβε (min_le_left _ _)
  have hβColumn : β < εColumn := lt_of_lt_of_le hβε (min_le_right _ _)
  have hAbsRow : |β| < εRow := by simpa [abs_of_pos hβ] using hβRow
  have hAbsColumn : |β| < εColumn := by simpa [abs_of_pos hβ] using hβColumn
  have hRowLt := hRow β hAbsRow
  have hColumnLt := hColumn β hAbsColumn
  constructor
  · rw [show row β =
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy by
        simpa [row] using
          finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension_eq_existing
            H β energyIdentity energyNontrivial hβ hEnergy] at hRowLt
    exact hRowLt
  · rw [show column β =
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy by
        simpa [column] using
          finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension_eq_existing
            H β energyIdentity energyNontrivial hβ hEnergy] at hColumnLt
    exact hColumnLt

/-- The fixed-volume posterior Dobrushin neighborhood packaged as a reusable
certificate.  The exact canonical envelope itself dominates every actual
Perron-posterior target-fiber influence matrix. -/
structure Z2FiniteEvenFourTorusPerronPosteriorFixedVolumeDobrushinPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  rowColumnStrict :
    ∀ β : ℝ, ∀ hβ : 0 < β, β < epsilon →
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy < (1 / 2 : ℝ) ∧
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy < (1 / 2 : ℝ)
  dominatesActual :
    ∀ β : ℝ, ∀ hβ : 0 < β, β < epsilon →
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
          H β energyIdentity energyNontrivial hβ hEnergy)

/-- Construct the fixed-volume strict posterior Dobrushin receipt. -/
noncomputable def z2FiniteEvenFourTorusPerronPosteriorFixedVolumeDobrushinPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusPerronPosteriorFixedVolumeDobrushinPackage
      H energyIdentity energyNontrivial hEnergy := by
  let hExists :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelope_exists_smallPositive_row_column_lt_half
      H energyIdentity energyNontrivial hEnergy
  let ε : ℝ := Classical.choose hExists
  have hSpec := Classical.choose_spec hExists
  exact
    { epsilon := ε
      epsilon_pos := hSpec.1
      rowColumnStrict := hSpec.2
      dominatesActual := by
        intro β hβ _hβε
        exact
          finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
            H β energyIdentity energyNontrivial hβ hEnergy }

end

end MathlibAnalytic
end MGAP4D
