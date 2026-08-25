import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopSpectralProjection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

/-- A non-top real spectral point of a positive compact operator is controlled by
its restriction to the orthogonal complement of the full eigenvalue-one space.

This is the key abstract isolation statement.  Mathlib's Fredholm alternative
turns every nonzero spectral point of the compact operator into an eigenvalue;
positivity makes that eigenvalue nonnegative; symmetry makes every eigenvector
with eigenvalue different from one orthogonal to the full fixed-point space;
and the ordinary operator norm of the canonical orthogonal restriction then
bounds that eigenvalue. -/
theorem realHilbertPositiveCompact_nonunit_spectralPoint_mem_Icc_topOrthogonalNorm
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hPositive : (S : E →ₗ[ℝ] E).IsPositive)
    (hCompact : IsCompactOperator S)
    {mu : ℝ}
    (hmuSpec : mu ∈ spectrum ℝ S)
    (hmuOne : mu ≠ 1) :
    mu ∈ Set.Icc 0
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hPositive.isSymmetric‖ := by
  by_cases hmuZero : mu = 0
  · subst mu
    exact ⟨le_rfl,
      norm_nonneg
        (realHilbertTopEigenspaceOrthogonalRestriction S hPositive.isSymmetric)⟩
  have hmuEig : HasEigenvalue (S : Module.End ℝ E) mu :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hCompact hmuZero).2 hmuSpec
  have hmuNonneg : 0 ≤ mu := by
    apply eigenvalue_nonneg_of_nonneg hmuEig
    intro x
    have hx := hPositive.re_inner_nonneg_left x
    simpa [real_inner_comm] using hx
  obtain ⟨v, hvEig, hvNe⟩ := hmuEig.exists_hasEigenvector
  have hvEig' : S v = mu • v :=
    Module.End.mem_genEigenspace_one.mp hvEig
  let F : Submodule ℝ E := realHilbertTopEigenspace S
  have hvOrth : v ∈ Fᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hxFix : S x = x :=
      (realHilbertTopEigenspace_mem S x).1 (by simpa [F] using hx)
    have hrel : inner ℝ x v = mu * inner ℝ x v := by
      calc
        inner ℝ x v = inner ℝ (S x) v := by rw [hxFix]
        _ = inner ℝ x (S v) := hPositive.isSymmetric x v
        _ = inner ℝ x (mu • v) := by rw [hvEig']
        _ = mu * inner ℝ x v := by simp [inner_smul_right]
    have hfactor : (1 - mu) * inner ℝ x v = 0 := by
      calc
        (1 - mu) * inner ℝ x v = inner ℝ x v - mu * inner ℝ x v := by ring
        _ = 0 := sub_eq_zero.mpr hrel
    have hcoeff : 1 - mu ≠ 0 := sub_ne_zero.mpr hmuOne.symm
    exact (mul_eq_zero.mp hfactor).resolve_left hcoeff
  let w : Fᗮ := ⟨v, hvOrth⟩
  have hwNe : w ≠ 0 := by
    intro hw
    apply hvNe
    have hcoe := congrArg (fun z : Fᗮ => (z : E)) hw
    simpa [w] using hcoe
  let R : Fᗮ →L[ℝ] Fᗮ :=
    realHilbertTopEigenspaceOrthogonalRestriction S hPositive.isSymmetric
  have hRw : R w = mu • w := by
    apply Subtype.ext
    simpa [R, w, F] using hvEig'
  have hOp := ContinuousLinearMap.le_opNorm R w
  rw [hRw, norm_smul, Real.norm_eq_abs, abs_of_nonneg hmuNonneg] at hOp
  have hwNormPos : 0 < ‖w‖ := norm_pos_iff.mpr hwNe
  have hmuLe : mu ≤ ‖R‖ := by
    nlinarith [hOp]
  exact ⟨hmuNonneg, by simpa [R, F] using hmuLe⟩

/-- The whole real spectrum of a positive compact operator splits into the
closed interval controlled by the excited-sector restriction and the single
full top spectral value `1`.  No simplicity of the top eigenspace is used. -/
theorem realHilbertPositiveCompact_spectrum_subset_topOrthogonalNorm_union_one
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hPositive : (S : E →ₗ[ℝ] E).IsPositive)
    (hCompact : IsCompactOperator S) :
    spectrum ℝ S ⊆
      Set.Icc 0
          ‖realHilbertTopEigenspaceOrthogonalRestriction S hPositive.isSymmetric‖ ∪
        ({1} : Set ℝ) := by
  intro mu hmu
  by_cases hmuOne : mu = 1
  · exact Or.inr (by simpa [hmuOne])
  · exact Or.inl
      (realHilbertPositiveCompact_nonunit_spectralPoint_mem_Icc_topOrthogonalNorm
        S hPositive hCompact hmu hmuOne)

local instance periodicHypercubicEvenSpecialUnitaryRealSpectrumIsolationPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The actual normalized finite Wilson physical transfer has real spectrum
contained in the excited interval `[0,q]` together with the top value `1`, where
`q` is exactly the norm of the already-constructed full-top-eigenspace
orthogonal restriction. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_subset_excitedInterval_union_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ⊆
      Set.Icc 0
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ ∪
        ({1} : Set ℝ) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator]
    using
      (realHilbertPositiveCompact_spectrum_subset_topOrthogonalNorm_union_one
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
          H N hN beta hbeta))

/-- The normalized Wilson top value `1` is genuinely in Mathlib's native real
spectrum, witnessed by the already-constructed unit physical top eigenvector. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_one_mem_real_spectrum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (1 : ℝ) ∈ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  have hOmegaNorm : ‖Omega‖ = 1 := by
    simpa [Omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
        H N hN beta hbeta
  have hOmegaNe : Omega ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hOmegaNorm
    norm_num at hOmegaNorm
  have hFix : S Omega = Omega := by
    simpa [S, Omega] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
        H N hN beta hbeta
  have hEig : HasEigenvalue (S : Module.End ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) 1 := by
    apply hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hOmegaNe⟩
    rw [Module.End.mem_genEigenspace_one]
    simpa using hFix
  rw [ContinuousLinearMap.spectrum_eq]
  exact hEig.mem_spectrum

/-- Above the strict excited-sector norm, the real spectrum consists of the
single top value `1`.  Thus `Ioi q` is an explicit open spectral-isolation
neighborhood supplied entirely by the genuine finite physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_inter_Ioi_excitedNorm_eq_singleton_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ∩
      Set.Ioi
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ =
      ({1} : Set ℝ) := by
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hq : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hsubset :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_subset_excitedInterval_union_one
      H N hN beta hbeta
  have hone :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_one_mem_real_spectrum
      H N hN beta hbeta
  ext mu
  constructor
  · rintro ⟨hmuSpec, hqmu⟩
    rcases hsubset hmuSpec with hlow | hone'
    · exact False.elim ((not_lt_of_ge hlow.2) (by simpa [q] using hqmu))
    · simpa using hone'
  · intro hmu
    have hmueq : mu = 1 := by simpa using hmu
    subst mu
    exact ⟨hone, by simpa [q] using hq⟩

/-- The whole open interval between the excited-sector norm and the top value
is in the native real resolvent set.  This is the explicit finite Wilson
spectral gap in resolvent language; it is not yet a continuum mass gap. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_Ioo_excitedNorm_one_subset_real_resolventSet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Set.Ioo
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖
        (1 : ℝ) ⊆
      resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) := by
  intro mu hmu
  have hnot : mu ∉ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
    intro hmuSpec
    have hhigh : mu ∈
        spectrum ℝ
            (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ∩
          Set.Ioi
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta‖ :=
      ⟨hmuSpec, hmu.1⟩
    have hone : mu ∈ ({1} : Set ℝ) := by
      rw [← periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_inter_Ioi_excitedNorm_eq_singleton_one
        H N hN beta hbeta]
      exact hhigh
    have hmueq : mu = 1 := by simpa using hone
    exact (ne_of_lt hmu.2) hmueq
  simpa [spectrum] using hnot

/-- Audit-visible finite-volume real spectral-isolation package.  It records
both the exact spectral split and the corresponding native resolvent interval,
with the strict separation inherited from the canonical full-top-eigenspace
orthogonal restriction. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRealSpectrumIsolationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  spectrumSubset :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ⊆
      Set.Icc 0
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ ∪
        ({1} : Set ℝ)
  oneInSpectrum :
    (1 : ℝ) ∈ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
  excitedNormLtOne :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1
  isolatedTopNeighborhood :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ∩
      Set.Ioi
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ =
      ({1} : Set ℝ)
  openGapInResolvent :
    Set.Ioo
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖
        (1 : ℝ) ⊆
      resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)

/-- Construct the exact finite Wilson real spectral-isolation package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRealSpectrumIsolationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRealSpectrumIsolationPackage
      H N hN beta hbeta :=
  { spectrumSubset :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_subset_excitedInterval_union_one
        H N hN beta hbeta
    oneInSpectrum :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_one_mem_real_spectrum
        H N hN beta hbeta
    excitedNormLtOne :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
    isolatedTopNeighborhood :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_inter_Ioi_excitedNorm_eq_singleton_one
        H N hN beta hbeta
    openGapInResolvent :=
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_Ioo_excitedNorm_one_subset_real_resolventSet
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
