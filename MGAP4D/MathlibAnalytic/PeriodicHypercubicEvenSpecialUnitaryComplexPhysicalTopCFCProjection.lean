import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTopSpectralProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

universe u

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- A continuous scalar selector which vanishes below the isolated spectral cut `q`
and takes the value one at the isolated top point `1`. -/
def realIsolatedTopCFCSelector (q x : ℝ) : ℝ :=
  max 0 ((x - q) / (1 - q))

/-- A globally continuous factor which witnesses that `1 - selector` is divisible
by `1 - x`.  The use of `max` avoids introducing a discontinuous piecewise inverse. -/
def realIsolatedTopCFCComplementFactor (q x : ℝ) : ℝ :=
  1 / max (1 - x) (1 - q)

/-- The isolated-top selector is globally continuous. -/
theorem realIsolatedTopCFCSelector_continuous (q : ℝ) :
    Continuous (realIsolatedTopCFCSelector q) := by
  unfold realIsolatedTopCFCSelector
  fun_prop

/-- Below the cut, the isolated-top selector vanishes exactly. -/
theorem realIsolatedTopCFCSelector_eq_zero_of_le
    {q x : ℝ} (hq : q < 1) (hx : x ≤ q) :
    realIsolatedTopCFCSelector q x = 0 := by
  have hden : 0 < 1 - q := sub_pos.mpr hq
  have hnum : x - q ≤ 0 := sub_nonpos.mpr hx
  have hfrac : (x - q) / (1 - q) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum hden.le
  simp [realIsolatedTopCFCSelector, max_eq_left hfrac]

/-- At the isolated top point, the selector is exactly one. -/
theorem realIsolatedTopCFCSelector_one
    {q : ℝ} (hq : q < 1) :
    realIsolatedTopCFCSelector q 1 = 1 := by
  have hden : 0 < 1 - q := sub_pos.mpr hq
  have hne : 1 - q ≠ 0 := ne_of_gt hden
  simp [realIsolatedTopCFCSelector, hne]

/-- On an excited interval together with the isolated top point, the selector
takes only the projection values zero and one. -/
theorem realIsolatedTopCFCSelector_eq_zero_or_one_of_mem_Iic_union_one
    {q x : ℝ} (hq : q < 1)
    (hx : x ∈ Set.Iic q ∪ ({1} : Set ℝ)) :
    realIsolatedTopCFCSelector q x = 0 ∨
      realIsolatedTopCFCSelector q x = 1 := by
  rcases hx with hx | hx
  · exact Or.inl (realIsolatedTopCFCSelector_eq_zero_of_le hq hx)
  · have hxOne : x = 1 := by simpa using hx
    subst x
    exact Or.inr (realIsolatedTopCFCSelector_one hq)

/-- On the isolated spectral set, the selector is idempotent pointwise. -/
theorem realIsolatedTopCFCSelector_mul_self
    {q x : ℝ} (hq : q < 1)
    (hx : x ∈ Set.Iic q ∪ ({1} : Set ℝ)) :
    realIsolatedTopCFCSelector q x * realIsolatedTopCFCSelector q x =
      realIsolatedTopCFCSelector q x := by
  rcases realIsolatedTopCFCSelector_eq_zero_or_one_of_mem_Iic_union_one hq hx with h | h
  · simp [h]
  · simp [h]

/-- Multiplication by the spectral coordinate fixes the selector on the isolated
spectral set. -/
theorem realIsolatedTopCFCSelector_coordinate_mul
    {q x : ℝ} (hq : q < 1)
    (hx : x ∈ Set.Iic q ∪ ({1} : Set ℝ)) :
    x * realIsolatedTopCFCSelector q x = realIsolatedTopCFCSelector q x := by
  rcases hx with hx | hx
  · rw [realIsolatedTopCFCSelector_eq_zero_of_le hq hx]
    simp
  · have hxOne : x = 1 := by simpa using hx
    subst x
    simp [realIsolatedTopCFCSelector_one hq]

/-- The complement factor is globally continuous whenever the spectral cut lies
strictly below one. -/
theorem realIsolatedTopCFCComplementFactor_continuous
    {q : ℝ} (hq : q < 1) :
    Continuous (realIsolatedTopCFCComplementFactor q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq
  have hne : ∀ x : ℝ, max (1 - x) (1 - q) ≠ 0 := by
    intro x
    have hpos : 0 < max (1 - x) (1 - q) :=
      lt_of_lt_of_le hden (le_max_right _ _)
    exact ne_of_gt hpos
  exact continuous_const.div (by fun_prop) hne

/-- Global scalar factorization of the selector complement.  This is the key
identity used to prove that the CFC projection acts identically on every fixed
vector, without assuming simplicity of the top eigenspace. -/
theorem realIsolatedTopCFCSelector_complement_factorization
    {q : ℝ} (hq : q < 1) (x : ℝ) :
    1 - realIsolatedTopCFCSelector q x =
      realIsolatedTopCFCComplementFactor q x * (1 - x) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq
  have hdenNe : 1 - q ≠ 0 := ne_of_gt hden
  by_cases hx : x ≤ q
  · have hxOne : x < 1 := lt_of_le_of_lt hx hq
    have hxden : 0 < 1 - x := sub_pos.mpr hxOne
    have hmax : max (1 - x) (1 - q) = 1 - x := by
      apply max_eq_left
      linarith
    rw [realIsolatedTopCFCSelector_eq_zero_of_le hq hx]
    simp [realIsolatedTopCFCComplementFactor, hmax, ne_of_gt hxden]
  · have hqx : q < x := lt_of_not_ge hx
    have hfrac : 0 ≤ (x - q) / (1 - q) := by
      exact div_nonneg (sub_nonneg.mpr hqx.le) hden.le
    have hmaxPhi : max 0 ((x - q) / (1 - q)) = (x - q) / (1 - q) :=
      max_eq_right hfrac
    have hmaxDen : max (1 - x) (1 - q) = 1 - q := by
      apply max_eq_right
      linarith
    simp only [realIsolatedTopCFCSelector, hmaxPhi,
      realIsolatedTopCFCComplementFactor, hmaxDen]
    field_simp [hdenNe]
    ring

/-- For a symmetric operator on a complex Hilbert space, a real continuous
functional calculus selector for an isolated top spectral point is exactly the
canonical orthogonal projection onto the full eigenvalue-one space.

This theorem is deliberately rank-free: the top eigenspace may have arbitrary
multiplicity. -/
theorem cfc_realIsolatedTopSelector_eq_complexHilbertTopEigenspaceProjection
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : E →L[ℂ] E)
    (hS : (S : E →ₗ[ℂ] E).IsSymmetric)
    (q : ℝ) (hq : q < 1)
    (hSpectrum : spectrum ℝ S ⊆ Set.Iic q ∪ ({1} : Set ℝ)) :
    cfc (realIsolatedTopCFCSelector q) S =
      complexHilbertTopEigenspaceProjection S := by
  let F := complexHilbertTopEigenspace S
  let P : E →L[ℂ] E := cfc (realIsolatedTopCFCSelector q) S
  let K : E →L[ℂ] E := cfc (realIsolatedTopCFCComplementFactor q) S
  letI : CompleteSpace F :=
    (complexHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hSA : IsSelfAdjoint S := hS.isSelfAdjoint
  have hPhiCont : ContinuousOn (realIsolatedTopCFCSelector q) (spectrum ℝ S) :=
    (realIsolatedTopCFCSelector_continuous q).continuousOn
  have hKCont : ContinuousOn (realIsolatedTopCFCComplementFactor q) (spectrum ℝ S) :=
    (realIsolatedTopCFCComplementFactor_continuous hq).continuousOn
  have hOneSubCont : ContinuousOn (fun x : ℝ => 1 - x) (spectrum ℝ S) := by
    fun_prop
  have hPhiIdem :
      (spectrum ℝ S).EqOn
        (fun x => realIsolatedTopCFCSelector q x * realIsolatedTopCFCSelector q x)
        (realIsolatedTopCFCSelector q) := by
    intro x hx
    exact realIsolatedTopCFCSelector_mul_self hq (hSpectrum hx)
  have hCoordPhi :
      (spectrum ℝ S).EqOn
        (fun x => x * realIsolatedTopCFCSelector q x)
        (realIsolatedTopCFCSelector q) := by
    intro x hx
    exact realIsolatedTopCFCSelector_coordinate_mul hq (hSpectrum hx)
  have hPmul : P * P = P := by
    calc
      P * P =
          cfc
            (fun x =>
              realIsolatedTopCFCSelector q x * realIsolatedTopCFCSelector q x) S := by
        simpa [P] using
          (cfc_mul (realIsolatedTopCFCSelector q) (realIsolatedTopCFCSelector q) S
            hPhiCont hPhiCont).symm
      _ = cfc (realIsolatedTopCFCSelector q) S := cfc_congr hPhiIdem
      _ = P := rfl
  have hPIdem : IsIdempotentElem P := hPmul
  have hPSelf : IsSelfAdjoint P := IsSelfAdjoint.cfc
  have hPStar : IsStarProjection P := ⟨hPIdem, hPSelf⟩
  have hSP : S * P = P := by
    change S * cfc (realIsolatedTopCFCSelector q) S =
      cfc (realIsolatedTopCFCSelector q) S
    have hid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S hSA
    calc
      S * cfc (realIsolatedTopCFCSelector q) S =
          cfc (id : ℝ → ℝ) S * cfc (realIsolatedTopCFCSelector q) S := by
        rw [hid]
      _ = cfc (fun x : ℝ => x * realIsolatedTopCFCSelector q x) S := by
        exact
          (cfc_mul (id : ℝ → ℝ) (realIsolatedTopCFCSelector q) S
            (by fun_prop) hPhiCont).symm
      _ = cfc (realIsolatedTopCFCSelector q) S := cfc_congr hCoordPhi
  have hOneSubP :
      (1 : E →L[ℂ] E) - P =
        cfc (fun x : ℝ => 1 - realIsolatedTopCFCSelector q x) S := by
    change (1 : E →L[ℂ] E) - cfc (realIsolatedTopCFCSelector q) S =
      cfc (fun x : ℝ => 1 - realIsolatedTopCFCSelector q x) S
    have hone : cfc (fun _ : ℝ => 1) S = (1 : E →L[ℂ] E) :=
      cfc_const_one ℝ S hSA
    calc
      (1 : E →L[ℂ] E) - cfc (realIsolatedTopCFCSelector q) S =
          cfc (fun _ : ℝ => 1) S - cfc (realIsolatedTopCFCSelector q) S := by
        rw [hone]
      _ = cfc (fun x : ℝ => 1 - realIsolatedTopCFCSelector q x) S := by
        exact
          (cfc_sub (fun _ : ℝ => 1) (realIsolatedTopCFCSelector q) S
            (by fun_prop) hPhiCont).symm
  have hOneSubS :
      (1 : E →L[ℂ] E) - S = cfc (fun x : ℝ => 1 - x) S := by
    have hone : cfc (fun _ : ℝ => 1) S = (1 : E →L[ℂ] E) :=
      cfc_const_one ℝ S hSA
    have hid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S hSA
    calc
      (1 : E →L[ℂ] E) - S =
          cfc (fun _ : ℝ => 1) S - cfc (id : ℝ → ℝ) S := by
        rw [hone, hid]
      _ = cfc (fun x : ℝ => 1 - x) S := by
        exact
          (cfc_sub (fun _ : ℝ => 1) (id : ℝ → ℝ) S
            (by fun_prop) (by fun_prop)).symm
  have hFactor :
      (1 : E →L[ℂ] E) - P = K * ((1 : E →L[ℂ] E) - S) := by
    calc
      (1 : E →L[ℂ] E) - P =
          cfc (fun x : ℝ => 1 - realIsolatedTopCFCSelector q x) S := hOneSubP
      _ = cfc
          (fun x : ℝ => realIsolatedTopCFCComplementFactor q x * (1 - x)) S := by
        apply cfc_congr
        intro x _
        exact realIsolatedTopCFCSelector_complement_factorization hq x
      _ = cfc (realIsolatedTopCFCComplementFactor q) S *
          cfc (fun x : ℝ => 1 - x) S :=
        cfc_mul (realIsolatedTopCFCComplementFactor q) (fun x : ℝ => 1 - x) S
          hKCont hOneSubCont
      _ = K * cfc (fun x : ℝ => 1 - x) S := rfl
      _ = K * ((1 : E →L[ℂ] E) - S) := by
        rw [hOneSubS]
  have hRangeSub : P.range ≤ F := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change P x ∈ complexHilbertTopEigenspace S
    apply (complexHilbertTopEigenspace_mem S (P x)).2
    have h := congrArg (fun T : E →L[ℂ] E => T x) hSP
    simpa using h
  have hTopSub : F ≤ P.range := by
    intro y hy
    have hyFix : S y = y := by
      exact (complexHilbertTopEigenspace_mem S y).1 (by simpa [F] using hy)
    have hApply := congrArg (fun T : E →L[ℂ] E => T y) hFactor
    have hResidual : y - P y = 0 := by
      simpa [hyFix] using hApply
    have hPfix : P y = y := (sub_eq_zero.mp hResidual).symm
    exact ⟨y, hPfix⟩
  have hRange : P.range = F := le_antisymm hRangeSub hTopSub
  have hQStar : IsStarProjection (complexHilbertTopEigenspaceProjection S) := by
    simpa [complexHilbertTopEigenspaceProjection, F] using
      (isStarProjection_starProjection (U := F))
  have hQRange : (complexHilbertTopEigenspaceProjection S).range = F := by
    simpa [complexHilbertTopEigenspaceProjection, F] using
      (Submodule.range_starProjection F)
  have hPQ : P = complexHilbertTopEigenspaceProjection S := by
    exact
      (ContinuousLinearMap.IsStarProjection.ext_iff hPStar hQStar).2
        (hRange.trans hQRange.symm)
  simpa [P] using hPQ

local instance periodicHypercubicEvenSpecialUnitaryComplexTopCFCRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexTopCFCComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The real scalar spectrum of the genuine complex transfer C⋆-algebra element
has the same isolated-top cut supplied by the native complex spectral theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_real_cfc_spectrum_subset_excitedIic_union_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ⊆
      Set.Iic
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ ∪
        ({1} : Set ℝ) := by
  let SC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hSymm :
      (SC : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsSymmetric := by
    simpa [SC] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
  have hSelf : IsSelfAdjoint SC := hSymm.isSelfAdjoint
  have hRestrict : SpectrumRestricts SC Complex.reCLM :=
    IsSelfAdjoint.spectrumRestricts (a := SC) hSelf
  have hComplexSubset :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_complex_spectrum_subset_excitedRealInterval_union_one
      H N hN beta hbeta
  intro mu hmu
  have hmuComplex : (mu : ℂ) ∈ spectrum ℂ SC := by
    have hImage : algebraMap ℝ ℂ mu ∈ algebraMap ℝ ℂ '' spectrum ℝ SC :=
      ⟨mu, hmu, rfl⟩
    rw [hRestrict.algebraMap_image] at hImage
    simpa using hImage
  have hmuComplex' :
      (mu : ℂ) ∈ spectrum ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) := by
    simpa [SC] using hmuComplex
  rcases hComplexSubset hmuComplex' with hlow | hone
  · rcases hlow with ⟨r, hr, hrmu⟩
    have hrmuReal : r = mu := by
      have h := congrArg Complex.re hrmu
      simpa using h
    have hmuLe : mu ≤ q := by
      simpa [q, hrmuReal] using hr.2
    exact Or.inl hmuLe
  · have hmuOneComplex : (mu : ℂ) = 1 := by simpa using hone
    have hmuOne : mu = 1 := by
      have h := congrArg Complex.re hmuOneComplex
      simpa using h
    exact Or.inr (by simpa [hmuOne])

/-- The isolated-top CFC projection of the genuine complex normalized Wilson
transfer operator. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  cfc
    (realIsolatedTopCFCSelector
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖)
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)

/-- The CFC selector at the isolated spectral point `1` is exactly Mathlib's
canonical orthogonal projection onto the entire complex top eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta := by
  let SC := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  have hq : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hSymm :
      (SC : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsSymmetric := by
    simpa [SC] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
  have hSpectrum : spectrum ℝ SC ⊆ Set.Iic q ∪ ({1} : Set ℝ) := by
    simpa [SC, q] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_real_cfc_spectrum_subset_excitedIic_union_one
        H N hN beta hbeta
  have hCFC :=
    cfc_realIsolatedTopSelector_eq_complexHilbertTopEigenspaceProjection
      SC hSymm q hq hSpectrum
  simpa [SC, q,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection] using hCFC

/-- Consequently the isolated-top CFC projection is also exactly the scalar
extension of the genuine real top spectral projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_eq_complexification
      H N hN beta hbeta

/-- The CFC projection has exactly the full top eigenspace as range. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_range
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta).range =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
  exact periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_range
    H N hN beta hbeta

/-- The isolated-top CFC element is a genuine star projection. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_isStarProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsStarProjection
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
  simp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection,
    complexHilbertTopEigenspaceProjection]

/-- Audit-visible package identifying the isolated spectral point `1` by
Mathlib's real continuous functional calculus. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTopCFCProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  realCFCSpectrumCut :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ⊆
      Set.Iic
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ ∪
        ({1} : Set ℝ)
  cfcProjectionCanonical :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta
  cfcProjectionComplexification :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta)
  cfcProjectionRange :
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta).range =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta

/-- Construct the exact isolated-top CFC projection package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTopCFCProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTopCFCProjectionPackage
      H N hN beta hbeta :=
  { realCFCSpectrumCut :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_real_cfc_spectrum_subset_excitedIic_union_one
        H N hN beta hbeta
    cfcProjectionCanonical :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection
        H N hN beta hbeta
    cfcProjectionComplexification :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification
        H N hN beta hbeta
    cfcProjectionRange :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_range
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
