import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMResolventLocalVanish
import Mathlib.Tactic

namespace LinearPMap

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- For a self-adjoint partially defined operator, surjectivity of a real shift
already forces injectivity.  Thus a functional-calculus construction of a
preimage for every target is enough to obtain the full algebraic resolvent. -/
theorem realShift_injective_of_surjective_of_selfAdjoint
    (A : E →ₗ.[ℝ] E)
    (hSelf : IsSelfAdjoint A)
    (lambda : ℝ)
    (hSurjective : Function.Surjective (A.realShift lambda)) :
    Function.Injective (A.realShift lambda) := by
  have hFormal : A.IsFormalAdjoint A := by
    have hAdjointFormal : A.adjoint.IsFormalAdjoint A :=
      A.adjoint_isFormalAdjoint hSelf.dense_domain
    rwa [(LinearPMap.isSelfAdjoint_def).mp hSelf] at hAdjointFormal
  have hShiftFormal (u v : A.domain) :
      inner ℝ (A.realShift lambda u) (v : E) =
        inner ℝ (u : E) (A.realShift lambda v) := by
    simpa only [LinearPMap.realShift_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right] using hFormal u v
  intro x y hxy
  let d : A.domain := x - y
  have hdShift : A.realShift lambda d = 0 := by
    dsimp [d]
    rw [(A.realShift lambda).map_sub, hxy, sub_self]
  obtain ⟨w, hw⟩ := hSurjective (d : E)
  have hdInner : inner ℝ (d : E) (d : E) = 0 := by
    calc
      inner ℝ (d : E) (d : E) =
          inner ℝ (d : E) (A.realShift lambda w) := by rw [hw]
      _ = inner ℝ (A.realShift lambda d) (w : E) :=
        (hShiftFormal d w).symm
      _ = 0 := by simp [hdShift]
  have hdNormSq : ‖(d : E)‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hdInner
  have hdZero : (d : E) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hdNormSq)
  apply Subtype.ext
  dsimp [d] at hdZero
  change (x : E) - (y : E) = 0 at hdZero
  exact sub_eq_zero.mp hdZero

/-- On a self-adjoint operator, algebraic bijectivity of a real shift is
therefore equivalent to surjectivity. -/
theorem realShift_bijective_iff_surjective_of_selfAdjoint
    (A : E →ₗ.[ℝ] E)
    (hSelf : IsSelfAdjoint A)
    (lambda : ℝ) :
    Function.Bijective (A.realShift lambda) ↔
      Function.Surjective (A.realShift lambda) := by
  constructor
  · exact fun h => h.2
  · intro hSurjective
    exact ⟨A.realShift_injective_of_surjective_of_selfAdjoint
      hSelf lambda hSurjective, hSurjective⟩

end

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Replace the remaining local resolvent/PVM equivalence by two concrete
functional-calculus constructions.

The first field constructs a domain preimage of a vector whose PVM vanishes on
an open neighborhood of the spectral parameter.  The second field proves that
surjectivity of the shifted Hamiltonian excludes every vector from local PVM
support.  Self-adjointness upgrades the generated surjectivity to bijectivity.
-/

/-- Local functional-calculus data for the actual canonical Hamiltonian on
`Ω⊥`.  The preimage field is the truncated reciprocal functional calculus
`(H-E)⁻¹`; the exclusion field is the converse local resolvent statement. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus
    (M : ExplicitWightmanOSReconstructedModel) where
  localVanish_has_preimage :
    ∀ (E : ℝ) (ψ : M.VacuumOrthogonalHilbert) (U : Set ℝ),
      E ∈ U → IsOpen U →
      M.spectralPVM.projection U (ψ : M.H) = 0 →
      ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        M.canonicalVacuumOrthogonalHamiltonian.realShift E x = ψ
  surjective_implies_vectorwise_localVanish :
    ∀ E : ℝ,
      Function.Surjective
          (M.canonicalVacuumOrthogonalHamiltonian.realShift E) →
        ∀ ψ : M.VacuumOrthogonalHilbert,
          ∃ U : Set ℝ, E ∈ U ∧ IsOpen U ∧
            M.spectralPVM.projection U (ψ : M.H) = 0

/-- Vectorwise local PVM vanishing produces surjectivity by applying the local
functional-calculus inverse to each target vector. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus.vectorwise_localVanish_implies_surjective
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus M)
    (E : ℝ)
    (hLocal :
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ U : Set ℝ, E ∈ U ∧ IsOpen U ∧
          M.spectralPVM.projection U (ψ : M.H) = 0) :
    Function.Surjective
      (M.canonicalVacuumOrthogonalHamiltonian.realShift E) := by
  intro ψ
  obtain ⟨U, hEU, hU, hZero⟩ := hLocal ψ
  exact F.localVanish_has_preimage E ψ U hEU hU hZero

/-- The two local functional-calculus constructions identify surjectivity of
`H|Ω⊥ - E I` with vectorwise local PVM vanishing. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus.realShift_surjective_iff_vectorwise_localVanish
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus M)
    (E : ℝ) :
    Function.Surjective
        (M.canonicalVacuumOrthogonalHamiltonian.realShift E) ↔
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ U : Set ℝ, E ∈ U ∧ IsOpen U ∧
          M.spectralPVM.projection U (ψ : M.H) = 0 := by
  constructor
  · exact F.surjective_implies_vectorwise_localVanish E
  · exact F.vectorwise_localVanish_implies_surjective E

/-- Self-adjointness upgrades the local functional calculus to the complete
resolvent/PVM compatibility package of the preceding layer. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus.toPVMResolventCompatibility
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian) :
    ExplicitWightmanOSCanonicalRestrictedPVMResolventCompatibility M :=
  { realShift_bijective_iff_vectorwise_pvm_localVanish := fun E => by
      constructor
      · intro hBijective
        exact F.surjective_implies_vectorwise_localVanish E hBijective.2
      · intro hLocal
        have hSurjective :=
          F.vectorwise_localVanish_implies_surjective E hLocal
        exact ⟨
          M.canonicalVacuumOrthogonalHamiltonian.
            realShift_injective_of_surjective_of_selfAdjoint
              hSelf E hSurjective,
          hSurjective⟩ }

/-- The local functional calculus and physical PVM-support identification now
generate the actual canonical restricted PVM spectral theorem. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus.toCanonicalRestrictedPVMSpectralTheorem
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (hSupport :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) :
    ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M :=
  (F.toPVMResolventCompatibility hSelf).
    toCanonicalRestrictedPVMSpectralTheorem hSupport

/-- Exact-gap PVM support endpoint generated from local functional calculus,
without taking the global operator-spectrum/PVM-support equivalence as input. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_local_functionalCalculus
    (M : ExplicitWightmanOSReconstructedModel)
    (F : ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hSupport :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp M
      ((F.toCanonicalRestrictedPVMSpectralTheorem hSelf hSupport).
        toCanonicalPVMOpenSupportBridge
          hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact
    explicit_wightman_os_exact_gap_pvm_open_support_of_resolvent_pvm_localVanish
      M (F.toPVMResolventCompatibility hSelf)
        hSelf D hGap hExactSpectrum hSupport

end

end MathlibAnalytic
end MGAP4D
