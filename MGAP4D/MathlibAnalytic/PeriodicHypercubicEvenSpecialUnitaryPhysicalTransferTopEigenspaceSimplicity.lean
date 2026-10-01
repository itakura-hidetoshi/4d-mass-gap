import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopModeSignRigidity
import Mathlib.Tactic

/-!
# Simplicity of the finite-volume physical Wilson top eigenspace

The previous two rigidity layers prove:

* every nonzero nonnegative full-top mode is strictly positive almost everywhere;
* every unit full-top mode has one fixed sign almost everywhere.

This file combines those facts with the already constructed strictly positive
normalized top mode Ω.

If a top mode had a nonzero component orthogonal to Ω, normalize that component.
Sign rigidity makes it one-signed. Strict positivity of Ω then forces a
nonzero inner product with Ω, contradicting orthogonality.

Therefore the entire eigenvalue-one sector of the normalized physical
finite-volume transfer is exactly one-dimensional.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- A strictly-positive real L² vector has strictly positive inner product with
every nonzero nonnegative real L² vector. -/
theorem realL2_inner_pos_of_ae_pos_ae_nonnegative_ne_zero
    {α : Type u} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (f g : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 < f x)
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hgNe : g ≠ 0) :
    0 < inner ℝ f g := by
  rw [MeasureTheory.L2.inner_def]
  have hNonneg :
      ∀ᵐ x ∂μ, 0 ≤ inner ℝ (f x) (g x) := by
    filter_upwards [hf, hg] with x hfx hgx
    simp only [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
      RCLike.re_to_real, conj_trivial]
    exact mul_nonneg hgx hfx.le
  have hInt : Integrable (fun x => inner ℝ (f x) (g x)) μ :=
    MeasureTheory.L2.integrable_inner f g
  have hNonnegIntegral :
      0 ≤ ∫ x, inner ℝ (f x) (g x) ∂μ :=
    integral_nonneg_of_ae hNonneg
  have hNe :
      (∫ x, inner ℝ (f x) (g x) ∂μ) ≠ 0 := by
    intro hZero
    have hPointZero :
        (fun x => inner ℝ (f x) (g x)) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg_ae hNonneg hInt).1 hZero
    have hgZeroAe :
        (fun x => g x) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hf, hPointZero] with x hfx hzero
      have hmul : g x * f x = 0 := by
        simpa [real_inner_eq_re_inner (𝕜 := ℝ), RCLike.inner_apply,
          RCLike.re_to_real, conj_trivial] using hzero
      exact (mul_eq_zero.mp hmul).resolve_right hfx.ne'
    have hgZero : g = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      simpa only [Pi.zero_apply] using hgZeroAe
    exact hgNe hgZero
  exact lt_of_le_of_ne hNonnegIntegral (Ne.symm hNe)

local instance physicalTopSimplicityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalTopSimplicityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalTopSimplicitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalTopSimplicityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalTopSimplicityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalTopSimplicitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section PhysicalTopSimplicity

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "μ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta

local notation "F" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta

local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta

/-- The full normalized physical top eigenspace is the one-dimensional span of
the canonical nonnegative top mode. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector :
    F = ℝ ∙ Omega := by
  have hOmegaNorm : ‖Omega‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  have hOmegaNormAmbient : ‖(Omega : Lp ℝ 2 μ)‖ = 1 := by
    simpa using hOmegaNorm
  have hOmegaPos :
      ∀ᵐ A ∂μ, 0 < (Omega : Lp ℝ 2 μ) A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
      H N hN beta hbeta
  have hTnorm :
      0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hOmegaTop : Omega ∈ F := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
    rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen]
    rw [smul_smul, inv_mul_cancel₀ hTnorm.ne', one_smul]
  apply le_antisymm
  · intro f hf
    let c : ℝ := inner ℝ Omega f
    let g : G := f - c • Omega
    have hgTop : g ∈ F := by
      exact
        Submodule.sub_mem F hf
          (Submodule.smul_mem F c hOmegaTop)
    have hgOrth : inner ℝ Omega g = 0 := by
      dsimp [g, c]
      rw [inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hOmegaNorm]
      ring
    have hgOrthAmbient :
        inner ℝ (Omega : Lp ℝ 2 μ) (g : Lp ℝ 2 μ) = 0 := by
      simpa using hgOrth
    have hgZero : g = 0 := by
      by_contra hgNe
      have hgNormPos : 0 < ‖g‖ := norm_pos_iff.mpr hgNe
      have hgNormPosAmbient : 0 < ‖(g : Lp ℝ 2 μ)‖ := by
        simpa using hgNormPos
      let a : ℝ := ‖(g : Lp ℝ 2 μ)‖⁻¹
      let u : G := a • g
      have ha : 0 < a := inv_pos.mpr hgNormPosAmbient
      have huTop : u ∈ F := by
        exact Submodule.smul_mem F a hgTop
      have huNorm : ‖u‖ = 1 := by
        change ‖a • (g : Lp ℝ 2 μ)‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        exact inv_mul_cancel₀ hgNormPosAmbient.ne'
      have huNe : u ≠ 0 := by
        intro huZero
        rw [huZero, norm_zero] at huNorm
        norm_num at huNorm
      have huOrth : inner ℝ Omega u = 0 := by
        dsimp [u]
        rw [real_inner_smul_right, hgOrth, mul_zero]
      have huOrthAmbient :
          inner ℝ (Omega : Lp ℝ 2 μ) (u : Lp ℝ 2 μ) = 0 := by
        simpa using huOrth
      rcases
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_unit_sign_rigidity
            H N hN beta hbeta u huTop huNorm with
        huNonneg | huNonpos
      · have huAmbientNe : (u : Lp ℝ 2 μ) ≠ 0 := by
          intro hzero
          apply huNe
          exact Subtype.ext hzero
        have hPos :
            0 < inner ℝ (Omega : Lp ℝ 2 μ) (u : Lp ℝ 2 μ) :=
          realL2_inner_pos_of_ae_pos_ae_nonnegative_ne_zero
            (Omega : Lp ℝ 2 μ) (u : Lp ℝ 2 μ)
            hOmegaPos huNonneg huAmbientNe
        have hZero :
            inner ℝ (Omega : Lp ℝ 2 μ) (u : Lp ℝ 2 μ) = 0 :=
          huOrthAmbient
        exact (ne_of_gt hPos) hZero
      · let v : G := -u
        have hvTop : v ∈ F := by
          exact Submodule.neg_mem F huTop
        have hvNe : v ≠ 0 := by
          intro hvZero
          apply huNe
          have h := congrArg Neg.neg hvZero
          simpa [v] using h
        have hvCoe :
            (fun A => (v : Lp ℝ 2 μ) A) =ᵐ[μ]
              fun A => -(u : Lp ℝ 2 μ) A := by
          dsimp [v]
          simpa only [Pi.neg_apply] using
            Lp.coeFn_neg (u : Lp ℝ 2 μ)
        have hvNonneg :
            ∀ᵐ A ∂μ, 0 ≤ (v : Lp ℝ 2 μ) A := by
          filter_upwards [hvCoe, huNonpos] with A hEq hA
          rw [hEq]
          exact neg_nonneg.mpr hA
        have hvAmbientNe : (v : Lp ℝ 2 μ) ≠ 0 := by
          intro hzero
          apply hvNe
          exact Subtype.ext hzero
        have hPos :
            0 < inner ℝ (Omega : Lp ℝ 2 μ) (v : Lp ℝ 2 μ) :=
          realL2_inner_pos_of_ae_pos_ae_nonnegative_ne_zero
            (Omega : Lp ℝ 2 μ) (v : Lp ℝ 2 μ)
            hOmegaPos hvNonneg hvAmbientNe
        have hvOrth : inner ℝ Omega v = 0 := by
          dsimp [v]
          rw [inner_neg_right, huOrth, neg_zero]
        have hvOrthAmbient :
            inner ℝ (Omega : Lp ℝ 2 μ) (v : Lp ℝ 2 μ) = 0 := by
          simpa using hvOrth
        have hZero :
            inner ℝ (Omega : Lp ℝ 2 μ) (v : Lp ℝ 2 μ) = 0 :=
          hvOrthAmbient
        exact (ne_of_gt hPos) hZero
    have hfEq : f = c • Omega := by
      dsimp [g] at hgZero
      exact sub_eq_zero.mp hgZero
    exact
      Submodule.mem_span_singleton.mpr
        ⟨c, hfEq.symm⟩
  · exact
      (Submodule.span_singleton_le_iff_mem Omega F).2 hOmegaTop

/-- Consequently the full top eigenspace is also the line generated by the
previously chosen normalized top eigenvector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_topEigenvector :
    F =
      ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta := by
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta
  have hF :
      F = ℝ ∙ Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector
      H N hN beta hbeta
  have homegaTop : omega ∈ F := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H N hN beta hbeta
  have homegaInOmegaSpan : omega ∈ ℝ ∙ Omega := by
    rw [← hF]
    exact homegaTop
  obtain ⟨c, hc⟩ :=
    Submodule.mem_span_singleton.mp homegaInOmegaSpan
  have hcNe : c ≠ 0 := by
    intro hcZero
    have homegaZero : omega = 0 := by
      rw [← hc, hcZero, zero_smul]
    have hnorm :
        ‖omega‖ = 1 := by
      simpa [omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
          H N hN beta hbeta
    rw [homegaZero, norm_zero] at hnorm
    norm_num at hnorm
  have hOmegaInOmegaChosen :
      Omega ∈ ℝ ∙ omega := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c⁻¹, ?_⟩
    calc
      c⁻¹ • omega = c⁻¹ • (c • Omega) := by rw [hc]
      _ = (c⁻¹ * c) • Omega := by rw [smul_smul]
      _ = Omega := by rw [inv_mul_cancel₀ hcNe, one_smul]
  have hSpan :
      ℝ ∙ Omega = ℝ ∙ omega := by
    apply le_antisymm
    · exact
        (Submodule.span_singleton_le_iff_mem Omega (ℝ ∙ omega)).2
          hOmegaInOmegaChosen
    · exact
        (Submodule.span_singleton_le_iff_mem omega (ℝ ∙ Omega)).2
          homegaInOmegaSpan
  simpa [omega] using hF.trans hSpan

/-- The older chosen-vacuum excitation sector is therefore exactly the
orthogonal complement of the full top eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal_eq_excitationSubmodule :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_topEigenvector]

end PhysicalTopSimplicity

end

end MathlibAnalytic
end MGAP4D
