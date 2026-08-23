import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferCompact
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

universe u

/-- A positive compact operator on a complete real Hilbert space has a unit
vector at its top operator-norm eigenvalue, provided one unit vector is already
available to witness nontriviality.

The nonzero-operator case is obtained without adding the missing compact
corollary to `Rayleigh.lean`: positivity forces every Rayleigh quotient to be
nonnegative, so if `‖T‖` were in the resolvent set then the uniform strict
Rayleigh bound there would contradict
`‖T‖ = ⨆ x, |rayleighQuotient T x|`.  Compact Fredholm theory then turns the
nonzero spectral point `‖T‖` into an eigenvalue.  The zero-operator case uses
the supplied unit vector. -/
theorem realHilbertPositiveCompact_exists_unit_topEigenvector
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (unit : E)
    (hunit : ‖unit‖ = 1)
    (hPositive : (T : E →ₗ[ℝ] E).IsPositive)
    (hCompact : IsCompactOperator T) :
    ∃ Ω : E, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω := by
  have hunit_ne : unit ≠ 0 := by
    intro h
    rw [h, norm_zero] at hunit
    norm_num at hunit
  letI : Nontrivial E := ⟨⟨unit, 0, hunit_ne⟩⟩
  by_cases hTzero : T = 0
  · refine ⟨unit, hunit, ?_⟩
    simp [hTzero]
  · have hnorm_pos : 0 < ‖T‖ := norm_pos_iff.mpr hTzero
    have hSymm : (T : E →ₗ[ℝ] E).IsSymmetric := hPositive.isSymmetric
    have hRayleighNonneg : ∀ x : E, 0 ≤ T.rayleighQuotient x := by
      intro x
      change 0 ≤ T.reApplyInnerSelf x / ‖x‖ ^ 2
      have hnum : 0 ≤ T.reApplyInnerSelf x := by
        simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using
          hPositive.re_inner_nonneg_left x
      exact div_nonneg hnum (sq_nonneg _)
    have hnorm_mem_spectrum : ‖T‖ ∈ spectrum ℝ T := by
      by_contra hnot
      have hres : ‖T‖ ∈ resolventSet ℝ T := by
        simpa [spectrum] using hnot
      obtain ⟨ε, hε_pos, hε⟩ :=
        T.rayleighQuotient_le_of_norm_mem_resolventSet hres
      have habs : ∀ x : E, |T.rayleighQuotient x| ≤ ‖T‖ - ε := by
        intro x
        rw [abs_of_nonneg (hRayleighNonneg x)]
        exact hε x
      have hsup : (⨆ x : E, |T.rayleighQuotient x|) ≤ ‖T‖ - ε :=
        ciSup_le habs
      rw [← T.norm_eq_iSup_rayleighQuotient hSymm] at hsup
      linarith
    have hEigenvalue : HasEigenvalue (T : Module.End ℝ E) ‖T‖ :=
      (hCompact.hasEigenvalue_iff_mem_spectrum (ne_of_gt hnorm_pos)).2
        hnorm_mem_spectrum
    obtain ⟨v, hv⟩ := hEigenvalue.exists_hasEigenvector
    have hv_ne : v ≠ 0 := hv.2
    have hv_apply : T v = ‖T‖ • v := by
      simpa using hv.apply_eq_smul
    let Ω : E := ‖v‖⁻¹ • v
    have hv_norm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv_ne
    have hΩ_norm : ‖Ω‖ = 1 := by
      simp [Ω, norm_smul, hv_norm_ne]
    refine ⟨Ω, hΩ_norm, ?_⟩
    dsimp [Ω]
    rw [map_smul, hv_apply]
    simp [smul_smul, mul_comm]

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaarTopEigen_isProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance periodicHypercubicEvenSpecialUnitaryPhysicalTopEigen_completeSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The constant-one vector in normalized spatial-slice Haar `L²` is fixed by
every actual lattice gauge pullback. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_const_one
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ)) =
      Lp.const 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneL2 : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  apply Lp.ext
  have hPull :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N γ oneL2
  have hConst : oneL2 =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa [oneL2] using
      (Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ)))
  have hConstPull :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N γ)
      .quasiMeasurePreserving.ae_eq hConst
  filter_upwards [hPull, hConstPull, hConst] with A hpull hpulled hone
  calc
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N γ oneL2 A =
      oneL2 (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) := hpull
    _ = 1 := by simpa using hpulled
    _ = oneL2 A := by simpa using hone.symm

/-- Canonical unit vector witnessing that the actual finite-volume Gauss-law
Hilbert space is nontrivial.  This is only a reference vector; no transfer
eigenvector property is asserted here. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ⟨Lp.const 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ), by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
    intro γ
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_const_one H N γ⟩

/-- The canonical constant Gauss-law vector has unit Haar-`L²` norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm
    (H N : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖ = 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change ‖Lp.const 2 μ (1 : ℝ)‖ = 1
  simpa [measureReal_def] using
    (Lp.norm_const (μ := μ) (p := 2) (c := (1 : ℝ)) (by norm_num))

/-- The actual positive compact physical one-slab transfer has a normalized
top eigenvector at eigenvalue equal to its operator norm.  No uniqueness or
strict positivity of that eigenvalue is claimed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_exists_unit_topEigenvector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∃ Ω : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      ‖Ω‖ = 1 ∧
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta Ω =
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ • Ω := by
  exact
    realHilbertPositiveCompact_exists_unit_topEigenvector
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isCompact
        H N hN beta hbeta)

/-- A chosen normalized top eigenvector of the actual physical one-slab
transfer.  This is a finite-volume vacuum candidate; no uniqueness statement
is built into the choice. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  Classical.choose
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_exists_unit_topEigenvector
      H N hN beta hbeta)

/-- The chosen physical top eigenvector is normalized. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta‖ = 1 :=
  (Classical.choose_spec
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_exists_unit_topEigenvector
      H N hN beta hbeta)).1

/-- The chosen physical top eigenvector has eigenvalue exactly the physical
one-slab transfer norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta :=
  (Classical.choose_spec
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_exists_unit_topEigenvector
      H N hN beta hbeta)).2

/-- Audit-visible finite-volume physical top-eigenvector receipt. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  referenceUnit :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖ = 1
  topEigenvectorUnit :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta‖ = 1
  topEigenvectorEquation :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta

/-- Construct the actual finite-volume physical top-eigenvector receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorPackage
      H N hN beta hbeta :=
  { referenceUnit :=
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
    topEigenvectorUnit :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
        H N hN beta hbeta
    topEigenvectorEquation :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
