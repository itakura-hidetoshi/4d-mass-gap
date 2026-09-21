import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Topology.Order
import Mathlib.Tactic

/-!
# Uniqueness of the finite-volume positive Wilson top ray

The canonical fixed-right response path introduced in the preceding theorem
units ultimately depends on the finite-volume physical top mode.  The existing
construction chose a top eigenvector abstractly and then took its pointwise
absolute value.  That is sufficient at each fixed coupling, but continuity in
the coupling requires that this choice cannot jump between distinct positive
top rays.

This file removes that ambiguity.

For any physical top eigenvector we build the same continuous RKHS-synthesis
representative used for the canonical vacuum.  If `p` is the already
constructed strictly-positive canonical representative and `g` is any other
continuous top representative, compactness gives a maximizer of `g / p`.
Subtracting that maximal multiple leaves a nonnegative top representative
which vanishes at the maximizing point.  Strict positivity of the Wilson
kernel says that every nonzero nonnegative vector is sent to a strictly
positive function, a contradiction.

Hence every finite-volume top eigenvector lies on the same real line as the
canonical positive vacuum.  No spectral gap, Poincare inequality, coercivity,
or mass-gap input is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance continuousVacuumTopRayUniquenessSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumTopRayUniquenessSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumTopRayUniquenessSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumTopRayUniquenessSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumTopRayUniquenessSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumTopRayUniquenessSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A nonzero nonnegative real `L²` vector on a probability space has
strictly positive integral.  This is the scale-free version of the normalized
lemma already used by the strict-positivity construction. -/
theorem realL2_integral_pos_of_ae_nonnegative_ne_zero
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfne : f ≠ 0) :
    0 < ∫ x, f x ∂μ := by
  have hnormPos : 0 < ‖f‖ := (norm_pos_iff.mpr hfne)
  let u : Lp ℝ 2 μ := ‖f‖⁻¹ • f
  have huNonneg : ∀ᵐ x ∂μ, 0 ≤ u x := by
    have hInvNonneg : 0 ≤ ‖f‖⁻¹ := (inv_pos.mpr hnormPos).le
    filter_upwards [hf, Lp.coeFn_smul ‖f‖⁻¹ f] with x hx hsmul
    change 0 ≤ u x
    rw [hsmul]
    exact mul_nonneg hInvNonneg hx
  have huNorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnormPos)]
    rw [inv_mul_cancel₀ hnormPos.ne']
  have huIntPos :
      0 < ∫ x, u x ∂μ :=
    realL2_integral_pos_of_ae_nonnegative_norm_one u huNonneg huNorm
  have hfInt : Integrable (fun x => f x) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hScale :
      (∫ x, u x ∂μ) = ‖f‖⁻¹ * ∫ x, f x ∂μ := by
    have hsmul := Lp.coeFn_smul ‖f‖⁻¹ f
    calc
      (∫ x, u x ∂μ) =
          ∫ x, ‖f‖⁻¹ * f x ∂μ := by
            apply integral_congr_ae
            filter_upwards [hsmul] with x hx
            simpa [u, smul_eq_mul] using hx
      _ = ‖f‖⁻¹ * ∫ x, f x ∂μ := by
            rw [integral_const_mul]
  rw [hScale] at huIntPos
  exact (mul_pos_iff.mp huIntPos).resolve_left (not_lt_of_ge (inv_nonneg.mpr (norm_nonneg f))) |>.2

/-- Continuous pointwise representative attached to an arbitrary physical
one-slab vector by the same normalized RKHS synthesis used for the canonical
vacuum. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta f) B

/-- The arbitrary-vector continuous representative is continuous in the
boundary configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
        H N hN beta hbeta f) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
  exact continuous_const.mul
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_continuous
      H N hN beta hbeta _)

/-- Pointwise kernel formula for the arbitrary-vector normalized synthesis. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_topNorm_mul_eq_integral_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
        H N hN beta hbeta f B =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f.1 A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
  change
    lambda *
        (lambda⁻¹ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              H N hN beta hbeta f) B) = _
  rw [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_analysis_eq_integral_kernel
      H N hN beta hbeta
      ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) B

/-- If `f` is a top eigenvector, its normalized synthesis is an almost
everywhere representative of `f` itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_ae_eq_of_topEigen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hfEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ • f) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
      H N hN beta hbeta f) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun B => f.1 B := by
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta f)
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hSynthesisAE :
      S =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta f) := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_coeFn
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta f)
  have hS :
      S =
        lambda •
          ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
    dsimp [S]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_eq_adjoint]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis]
    have hval := congrArg Subtype.val hfEigen
    simpa [lambda] using hval
  have hScalarAE :=
    Lp.coeFn_smul lambda
      (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  filter_upwards [hSynthesisAE, hScalarAE] with B hSyn hSmul
  have hSynEq :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta f) B =
        lambda * f.1 B := by
    have hSB :
        S B =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
              H N hN beta hbeta f) B := hSyn
    rw [hS] at hSB
    have hSmul' :
        (lambda •
          (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))) B =
          lambda * f.1 B := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hSmul
    exact hSB.symm.trans hSmul'
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
  rw [hSynEq]
  field_simp [hlambda.ne']

/-- The canonical continuous vacuum representative is exactly the arbitrary
top-representative construction applied to the chosen nonnegative top vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_nonnegativeTop_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta := by
  rfl

/-- The full finite-volume physical top eigenspace is one-dimensional: every
top eigenvector is a real scalar multiple of the canonical strictly-positive
nonnegative top vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eq_smul_nonnegativeTop
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hgEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta g =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ • g) :
    ∃ c : ℝ,
      g =
        c •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta := by
  classical
  let p :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta
  let pC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let gC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative
      H N hN beta hbeta g
  let lambda :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hpCContinuous : Continuous pC := by
    simpa [pC] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H N hN beta hbeta
  have hgCContinuous : Continuous gC := by
    simpa [gC] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_continuous
        H N hN beta hbeta g
  have hpCPos : ∀ B, 0 < pC B := by
    intro B
    simpa [pC] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta B
  let ratio : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun B => gC B / pC B
  have hRatioContinuous : Continuous ratio := by
    dsimp [ratio]
    exact hgCContinuous.div hpCContinuous (fun B => ne_of_gt (hpCPos B))
  obtain ⟨B0, _hB0, hmax⟩ :=
    isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty :
        (Set.univ :
          Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)).Nonempty)
      hRatioContinuous.continuousOn
  let c : ℝ := ratio B0
  let h : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
    c • p - g
  let hC : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun B => c * pC B - gC B
  have hhCNonneg : ∀ B, 0 ≤ hC B := by
    intro B
    have hratio : ratio B ≤ c := by
      simpa [c] using hmax (Set.mem_univ B)
    have hmul : gC B ≤ c * pC B := by
      apply (div_le_iff₀ (hpCPos B)).mp
      simpa [ratio] using hratio
    simpa [hC] using sub_nonneg.mpr hmul
  have hhCB0 : hC B0 = 0 := by
    change c * pC B0 - gC B0 = 0
    rw [sub_eq_zero]
    dsimp [c, ratio]
    exact div_mul_cancel₀ (gC B0) (ne_of_gt (hpCPos B0))
  have hpAE :
      pC =ᵐ[μ] fun B => p.1 B := by
    simpa [pC, p, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
        H N hN beta hbeta
  have hgAE :
      gC =ᵐ[μ] fun B => g.1 B := by
    simpa [gC, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_ae_eq_of_topEigen
        H N hN beta hbeta g hgEigen
  have hhAE :
      hC =ᵐ[μ] fun B => h.1 B := by
    filter_upwards [hpAE, hgAE] with B hpB hgB
    simp [hC, h, hpB, hgB, smul_eq_mul]
  have hhNonneg : ∀ᵐ B ∂μ, 0 ≤ h.1 B := by
    filter_upwards [hhAE] with B hEq
    rw [← hEq]
    exact hhCNonneg B
  by_cases hhZero : h = 0
  · refine ⟨c, ?_⟩
    exact (sub_eq_zero.mp hhZero).symm
  · have hhLpNe :
        ((h : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 μ) ≠ 0 := by
        intro hz
        apply hhZero
        apply Subtype.ext
        exact hz
    have hhIntegralPos :
        0 < ∫ A, h.1 A ∂μ := by
      exact
        realL2_integral_pos_of_ae_nonnegative_ne_zero
          (((h : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ))
          hhNonneg hhLpNe
    obtain ⟨m, hmPos, hm⟩ :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_exists_uniform_pos_lower_bound
        H N beta
    have hhInt : Integrable (fun A => h.1 A) μ := by
      rw [← memLp_one_iff_integrable]
      exact
        (Lp.memLp
          (((h : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ))).mono_exponent (by norm_num)
    have hhKInt :
        Integrable
          (fun A =>
            h.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0) μ := by
      simpa [μ] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
          H N hN beta hbeta
          (((h : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ)) B0
    have hLower :
        m * (∫ A, h.1 A ∂μ) ≤
          ∫ A,
            h.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hhInt.const_mul m) hhKInt
      filter_upwards [hhNonneg] with A hA
      calc
        m * h.1 A = h.1 A * m := by ring
        _ ≤
          h.1 A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A B0 :=
          mul_le_mul_of_nonneg_left (hm A B0) hA
    have hIntegralPos :
        0 <
          ∫ A,
            h.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ :=
      lt_of_lt_of_le (mul_pos hmPos hhIntegralPos) hLower
    have hpEigPoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
        H N hN beta hbeta B0
    have hgEigPoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousTopRepresentative_topNorm_mul_eq_integral_kernel
        H N hN beta hbeta g B0
    have hIntegralEq :
        ∫ A,
            h.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ =
          lambda * hC B0 := by
      have hpKInt :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
          H N hN beta hbeta
          (((p : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ)) B0
      have hgKInt :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
          H N hN beta hbeta
          (((g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ)) B0
      have hpEigPoint' :
          lambda * pC B0 =
            ∫ A, p.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ := by
        simpa [lambda, pC, p, μ] using hpEigPoint
      have hgEigPoint' :
          lambda * gC B0 =
            ∫ A, g.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ := by
        simpa [lambda, gC, μ] using hgEigPoint
      calc
        (∫ A,
            h.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ) =
          ∫ A,
            (c * p.1 A - g.1 A) *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ := by
            apply integral_congr_ae
            filter_upwards with A
            rfl
        _ =
          c * (∫ A, p.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ) -
            ∫ A, g.1 A *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta A B0 ∂μ := by
            have hcpInt :
                Integrable
                  (fun A =>
                    c *
                      (p.1 A *
                        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                          H N beta A B0)) μ :=
              hpKInt.const_mul c
            calc
              (∫ A,
                (c * p.1 A - g.1 A) *
                  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta A B0 ∂μ) =
                ∫ A,
                  c *
                      (p.1 A *
                        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                          H N beta A B0) -
                    g.1 A *
                      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                        H N beta A B0 ∂μ := by
                    apply integral_congr_ae
                    filter_upwards with A
                    ring
              _ =
                (∫ A,
                  c *
                    (p.1 A *
                      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                        H N beta A B0) ∂μ) -
                  ∫ A, g.1 A *
                    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                      H N beta A B0 ∂μ := by
                    rw [integral_sub hcpInt hgKInt]
              _ = _ := by
                    rw [integral_const_mul]
        _ = c * (lambda * pC B0) - lambda * gC B0 := by
              rw [← hpEigPoint', ← hgEigPoint']
        _ = lambda * hC B0 := by
              simp [hC]
              ring
    rw [hhCB0] at hIntegralEq
    simp at hIntegralEq
    rw [hIntegralEq] at hIntegralPos
    exact (lt_irrefl 0) hIntegralPos

end

end MathlibAnalytic
end MGAP4D
