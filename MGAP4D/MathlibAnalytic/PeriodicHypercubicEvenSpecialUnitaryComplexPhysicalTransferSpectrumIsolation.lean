import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferRealSpectrumIsolation
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexSpectrumIsolationRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexSpectrumIsolationComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- Every nonzero spectral point of the genuine complex normalized physical
transfer is real, and its real part is already a spectral point of the genuine
real physical transfer.  The proof uses compactness to obtain a complex
physical eigenvector, symmetry to force the eigenvalue onto the real axis, and
the exact real/imaginary component intertwining to recover a nonzero real
physical eigenvector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_nonzero_spectralPoint_realPart_mem_real_spectrum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {z : ℂ}
    (hzSpec : z ∈ spectrum ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta))
    (hzZero : z ≠ 0) :
    (z.re : ℂ) = z ∧
      z.re ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let SC := periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N S
  have hCompact : IsCompactOperator SC := by
    simpa [SC, S,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator]
      using
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isCompact
          H N hN beta hbeta
  have hSymm :
      (SC : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsSymmetric := by
    simpa [SC, S,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator]
      using
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
          H N hN beta hbeta
  have hzSpec' : z ∈ spectrum ℂ SC := by
    simpa [SC, S,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator]
      using hzSpec
  have hzEig : HasEigenvalue
      (SC : Module.End ℂ
        (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) z :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hCompact hzZero).2 hzSpec'
  have hzConj : starRingEnd ℂ z = z :=
    hSymm.conj_eigenvalue_eq_self hzEig
  have hzReal : (z.re : ℂ) = z :=
    RCLike.conj_eq_iff_re.mp hzConj
  have hzIm : z.im = 0 := by
    have h := congrArg Complex.im hzReal
    simpa using h
  obtain ⟨v, hvEig, hvNe⟩ := hzEig.exists_hasEigenvector
  have hvEq : SC v = z • v :=
    Module.End.mem_genEigenspace_one.mp hvEig
  let vr := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N v
  let vi := periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N v
  have hvr : S vr = z.re • vr := by
    have h := congrArg
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N) hvEq
    simpa [SC, vr, vi,
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_smul, hzIm] using h
  have hvi : S vi = z.re • vi := by
    have h := congrArg
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N) hvEq
    simpa [SC, vr, vi,
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_smul, hzIm] using h
  have hcomponent : vr ≠ 0 ∨ vi ≠ 0 := by
    by_contra hnone
    rw [not_or] at hnone
    rcases hnone with ⟨hvr0, hvi0⟩
    apply hvNe
    have hvr0' :
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N v = 0 := by
      simpa [vr] using hvr0
    have hvi0' :
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N v = 0 := by
      simpa [vi] using hvi0
    rw [← periodicHypercubicEvenSpecialUnitaryComplexPhysical_reconstruct H N v,
      hvr0', hvi0']
    simp
  have hRealEig : HasEigenvalue
      (S : Module.End ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
      z.re := by
    rcases hcomponent with hvrNe | hviNe
    · apply hasEigenvalue_of_hasEigenvector
      refine ⟨?_, hvrNe⟩
      rw [Module.End.mem_genEigenspace_one]
      exact hvr
    · apply hasEigenvalue_of_hasEigenvector
      refine ⟨?_, hviNe⟩
      rw [Module.End.mem_genEigenspace_one]
      exact hvi
  have hRealSpec : z.re ∈ spectrum ℝ S := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact hRealEig.mem_spectrum
  exact ⟨hzReal, by simpa [S] using hRealSpec⟩

/-- The genuine complex spectrum is exactly constrained by the already-proved
real excited interval: every complex spectral point lies on the real axis in
the embedded interval `[0,q]`, apart from the top value `1`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_subset_excitedRealInterval_union_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    spectrum ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ⊆
      ((fun mu : ℝ => (mu : ℂ)) ''
          Set.Icc 0
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta‖) ∪
        ({1} : Set ℂ) := by
  intro z hzSpec
  by_cases hzZero : z = 0
  · exact Or.inl ⟨0,
      ⟨le_rfl,
        norm_nonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta)⟩,
      by simpa [hzZero]⟩
  have hzReal :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_nonzero_spectralPoint_realPart_mem_real_spectrum
      H N hN beta hbeta hzSpec hzZero
  have hRealSubset :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_subset_excitedInterval_union_one
      H N hN beta hbeta
  rcases hRealSubset hzReal.2 with hlow | hone
  · exact Or.inl ⟨z.re, hlow, hzReal.1⟩
  · have hrez : z.re = 1 := by simpa using hone
    have hcast : (z.re : ℂ) = (1 : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hrez
    have hzOne : z = 1 := hzReal.1.symm.trans hcast
    exact Or.inr (by simpa [hzOne])

/-- The normalized top vector witnesses `1` in the native complex spectrum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_one_mem_complex_spectrum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (1 : ℂ) ∈ spectrum ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
  let SC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Omega := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  have hOmegaNorm : ‖Omega‖ = 1 := by
    simpa [Omega] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenvector_norm
        H N hN beta hbeta
  have hOmegaNe : Omega ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hOmegaNorm
    norm_num at hOmegaNorm
  have hFix : SC Omega = Omega := by
    simpa [SC, Omega] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
        H N hN beta hbeta
  have hEig : HasEigenvalue
      (SC : Module.End ℂ
        (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) 1 := by
    apply hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hOmegaNe⟩
    rw [Module.End.mem_genEigenspace_one]
    simpa using hFix
  rw [ContinuousLinearMap.spectrum_eq]
  exact hEig.mem_spectrum

/-- Above the real excited-sector norm, the native complex spectrum contains
only the top point `1`.  In particular, the entire nonreal part of this right
half-plane is resolvent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_inter_rightHalfPlane_eq_singleton_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    spectrum ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ∩
      {z : ℂ |
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re} =
      ({1} : Set ℂ) := by
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hq : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hsubset :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_subset_excitedRealInterval_union_one
      H N hN beta hbeta
  have hone :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_one_mem_complex_spectrum
      H N hN beta hbeta
  ext z
  constructor
  · rintro ⟨hzSpec, hzq⟩
    rcases hsubset hzSpec with hlow | hone'
    · rcases hlow with ⟨mu, hmu, hmuz⟩
      have hzre : z.re = mu := by
        rw [← hmuz]
        simp
      have hqmu : q < mu := by simpa [hzre] using hzq
      exact False.elim ((not_lt_of_ge hmu.2) hqmu)
    · simpa using hone'
  · intro hz
    have hzOne : z = 1 := by simpa using hz
    subst z
    exact ⟨hone, by simpa [q] using hq⟩

/-- The right half-plane above the excited norm, punctured only at the top
spectral point, lies in the native complex resolvent set. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rightHalfPlane_except_one_subset_complex_resolventSet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    {z : ℂ |
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re ∧ z ≠ 1} ⊆
      resolventSet ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) := by
  intro z hz
  have hnot : z ∉ spectrum ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
    intro hzSpec
    have hhigh : z ∈
        spectrum ℂ
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ∩
          {w : ℂ |
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta‖ < w.re} :=
      ⟨hzSpec, hz.1⟩
    have hone : z ∈ ({1} : Set ℂ) := by
      rw [← periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_inter_rightHalfPlane_eq_singleton_one
        H N hN beta hbeta]
      exact hhigh
    have hzOne : z = 1 := by simpa using hone
    exact hz.2 hzOne
  simpa [spectrum] using hnot

/-- Audit-visible finite-volume complex spectral-isolation package on the
genuine complex Gauss-law physical Hilbert carrier. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabSpectrumIsolationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  spectrumSubset :
    spectrum ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ⊆
      ((fun mu : ℝ => (mu : ℂ)) ''
          Set.Icc 0
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta‖) ∪
        ({1} : Set ℂ)
  oneInSpectrum :
    (1 : ℂ) ∈ spectrum ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
  excitedNormLtOne :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1
  isolatedTopRightHalfPlane :
    spectrum ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ∩
      {z : ℂ |
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re} =
      ({1} : Set ℂ)
  puncturedRightHalfPlaneInResolvent :
    {z : ℂ |
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re ∧ z ≠ 1} ⊆
      resolventSet ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)

/-- Construct the exact finite Wilson complex spectral-isolation package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabSpectrumIsolationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabSpectrumIsolationPackage
      H N hN beta hbeta :=
  { spectrumSubset :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_subset_excitedRealInterval_union_one
        H N hN beta hbeta
    oneInSpectrum :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_one_mem_complex_spectrum
        H N hN beta hbeta
    excitedNormLtOne :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
    isolatedTopRightHalfPlane :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_inter_rightHalfPlane_eq_singleton_one
        H N hN beta hbeta
    puncturedRightHalfPlaneInResolvent :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rightHalfPlane_except_one_subset_complex_resolventSet
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
