import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMResolventLocalVanish
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
    simp only [LinearPMap.realShift_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hFormal u v]
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
          LinearPMap.realShift_injective_of_surjective_of_selfAdjoint
            M.canonicalVacuumOrthogonalHamiltonian hSelf E hSurjective,
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
  ExplicitWightmanOSCanonicalRestrictedPVMResolventCompatibility.toCanonicalRestrictedPVMSpectralTheorem
    (F.toPVMResolventCompatibility hSelf) hSupport

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
      ((F.toCanonicalRestrictedPVMSpectralTheorem hSelf hSupport).toCanonicalPVMOpenSupportBridge hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact
    explicit_wightman_os_exact_gap_pvm_open_support_of_resolvent_pvm_localVanish
      M (F.toPVMResolventCompatibility hSelf)
        hSelf D hGap hExactSpectrum hSupport

/-!
The remaining local functional-calculus boundary can be normalized to metric
balls and one explicit bounded Borel function.  This avoids taking an arbitrary
open-set inverse as primitive.
-/

/-- The quadratic form of an orthogonal spectral projection is the squared norm
of the projected vector. -/
theorem OrthogonalProjectionValuedSetFunction.inner_projection_self_eq_norm_sq
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (x : H) :
    inner ℝ (P.projection s x) x = ‖P.projection s x‖ ^ 2 := by
  calc
    inner ℝ (P.projection s x) x =
        inner ℝ (P.projection s (P.projection s x)) x := by
      rw [P.idempotent s x]
    _ = inner ℝ (P.projection s x) (P.projection s x) :=
      P.selfAdjoint s (P.projection s x) x
    _ = ‖P.projection s x‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]

/-- Projection vanishing descends along set inclusion.  Finite additivity,
self-adjointness, and idempotence suffice. -/
theorem OrthogonalProjectionValuedSetFunction.projection_eq_zero_of_subset
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {s t : Set ℝ} (hst : s ⊆ t) (x : H)
    (htZero : P.projection t x = 0) :
    P.projection s x = 0 := by
  have hDisjoint : Disjoint s (t \ s) := by
    refine Set.disjoint_left.2 ?_
    intro y hys hyDiff
    exact hyDiff.2 hys
  have hUnion : s ∪ (t \ s) = t := by
    ext y
    constructor
    · intro hy
      rcases hy with hys | hyDiff
      · exact hst hys
      · exact hyDiff.1
    · intro hyt
      by_cases hys : y ∈ s
      · exact Or.inl hys
      · exact Or.inr ⟨hyt, hys⟩
  have hAdd := P.disjoint_additive s (t \ s) hDisjoint x
  rw [hUnion] at hAdd
  have hInner :
      inner ℝ (P.projection s x) x +
          inner ℝ (P.projection (t \ s) x) x = 0 := by
    have h := congrArg (fun z : H => inner ℝ z x) hAdd
    simpa only [inner_add_left, htZero, inner_zero_left] using h.symm
  rw [P.inner_projection_self_eq_norm_sq s x,
    P.inner_projection_self_eq_norm_sq (t \ s) x] at hInner
  have hNormSq : ‖P.projection s x‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖P.projection s x‖,
      sq_nonneg ‖P.projection (t \ s) x‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hNormSq)

/-- Open-neighborhood projection vanishing refines to a positive-radius ball. -/
theorem OrthogonalProjectionValuedSetFunction.exists_ball_projection_eq_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {E : ℝ} {U : Set ℝ} (hU : IsOpen U) (hEU : E ∈ U)
    (x : H) (hZero : P.projection U x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball E ε ⊆ U ∧
      P.projection (Metric.ball E ε) x = 0 := by
  rcases Metric.isOpen_iff.1 hU E hEU with ⟨ε, hε, hBall⟩
  exact ⟨ε, hε, hBall,
    P.projection_eq_zero_of_subset hBall x hZero⟩

/-- The reciprocal of the shifted coordinate, truncated to zero on a ball
around its singularity. -/
def spectralBallTruncatedReciprocal (E ε t : ℝ) : ℝ :=
  if dist t E < ε then 0 else (t - E)⁻¹

@[simp] theorem spectralBallTruncatedReciprocal_of_mem
    {E ε t : ℝ} (ht : t ∈ Metric.ball E ε) :
    spectralBallTruncatedReciprocal E ε t = 0 := by
  have hdist : dist t E < ε := Metric.mem_ball.mp ht
  simp [spectralBallTruncatedReciprocal, hdist]

@[simp] theorem spectralBallTruncatedReciprocal_of_not_mem
    {E ε t : ℝ} (ht : t ∉ Metric.ball E ε) :
    spectralBallTruncatedReciprocal E ε t = (t - E)⁻¹ := by
  have hdist : ¬dist t E < ε := by
    simpa only [Metric.mem_ball] using ht
  simp [spectralBallTruncatedReciprocal, hdist]

/-- Outside the removed ball, the shifted coordinate cancels the truncated
reciprocal. -/
theorem sub_mul_spectralBallTruncatedReciprocal
    {E ε t : ℝ} (hε : 0 < ε) (ht : t ∉ Metric.ball E ε) :
    (t - E) * spectralBallTruncatedReciprocal E ε t = 1 := by
  have hdist : ¬dist t E < ε := by
    simpa only [Metric.mem_ball] using ht
  have htE : t ≠ E := by
    intro h
    subst t
    exact ht (Metric.mem_ball_self hε)
  have hsub : t - E ≠ 0 := sub_ne_zero.mpr htE
  simp [spectralBallTruncatedReciprocal, hdist, hsub]

/-- The ball-truncated reciprocal is Borel measurable. -/
theorem measurable_spectralBallTruncatedReciprocal
    (E ε : ℝ) :
    Measurable (spectralBallTruncatedReciprocal E ε) := by
  classical
  change Measurable fun t : ℝ =>
    if t ∈ Metric.ball E ε then 0 else (t - E)⁻¹
  exact Measurable.ite Metric.isOpen_ball.measurableSet
    measurable_const ((measurable_id.sub measurable_const).inv)

/-- The ball-truncated reciprocal has the sharp uniform bound `ε⁻¹`. -/
theorem norm_spectralBallTruncatedReciprocal_le
    {E ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖spectralBallTruncatedReciprocal E ε t‖ ≤ ε⁻¹ := by
  by_cases hdist : dist t E < ε
  · have hInvNonneg : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
    simpa [spectralBallTruncatedReciprocal, hdist] using hInvNonneg
  · have hdistLower : ε ≤ dist t E := le_of_not_gt hdist
    have habs : ε ≤ |t - E| := by
      simpa [Real.dist_eq] using hdistLower
    have hReciprocal : 1 / |t - E| ≤ 1 / ε :=
      one_div_le_one_div_of_le hε habs
    simpa [spectralBallTruncatedReciprocal, hdist, Real.norm_eq_abs,
      abs_inv, one_div] using hReciprocal

/-- Ball-local functional calculus for the actual canonical Hamiltonian. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus
    (M : ExplicitWightmanOSReconstructedModel) where
  ballVanish_has_preimage :
    ∀ (E ε : ℝ), 0 < ε →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0 →
        ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
          M.canonicalVacuumOrthogonalHamiltonian.realShift E x = ψ
  surjective_has_uniform_zero_ball :
    ∀ E : ℝ,
      Function.Surjective
          (M.canonicalVacuumOrthogonalHamiltonian.realShift E) →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ ψ : M.VacuumOrthogonalHilbert,
            M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0

/-- Ball-local inversion generates the arbitrary-open local inverse. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus.localVanish_has_preimage
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M)
    (E : ℝ) (ψ : M.VacuumOrthogonalHilbert) (U : Set ℝ)
    (hEU : E ∈ U) (hU : IsOpen U)
    (hZero : M.spectralPVM.projection U (ψ : M.H) = 0) :
    ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
      M.canonicalVacuumOrthogonalHamiltonian.realShift E x = ψ := by
  obtain ⟨ε, hε, _hBall, hBallZero⟩ :=
    M.spectralPVM.exists_ball_projection_eq_zero hU hEU (ψ : M.H) hZero
  exact B.ballVanish_has_preimage E ε hε ψ hBallZero

/-- A uniform zero projection on a resolvent ball gives vectorwise local PVM
vanishing. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus.surjective_implies_vectorwise_localVanish
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M)
    (E : ℝ)
    (hSurjective : Function.Surjective
      (M.canonicalVacuumOrthogonalHamiltonian.realShift E)) :
    ∀ ψ : M.VacuumOrthogonalHilbert,
      ∃ U : Set ℝ, E ∈ U ∧ IsOpen U ∧
        M.spectralPVM.projection U (ψ : M.H) = 0 := by
  obtain ⟨ε, hε, hZero⟩ :=
    B.surjective_has_uniform_zero_ball E hSurjective
  intro ψ
  exact ⟨Metric.ball E ε, Metric.mem_ball_self hε,
    Metric.isOpen_ball, hZero ψ⟩

/-- The ball calculus generates the preceding local functional-calculus package. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus.toLocalFunctionalCalculus
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M) :
    ExplicitWightmanOSCanonicalRestrictedPVMLocalFunctionalCalculus M :=
  { localVanish_has_preimage := B.localVanish_has_preimage
    surjective_implies_vectorwise_localVanish :=
      B.surjective_implies_vectorwise_localVanish }

/-- Ball functional calculus generates complete resolvent/PVM compatibility. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus.toPVMResolventCompatibility
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian) :
    ExplicitWightmanOSCanonicalRestrictedPVMResolventCompatibility M :=
  B.toLocalFunctionalCalculus.toPVMResolventCompatibility hSelf

/-- Ball functional calculus generates the canonical restricted PVM spectral
theorem. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus.toCanonicalRestrictedPVMSpectralTheorem
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (hSupport :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) :
    ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M :=
  B.toLocalFunctionalCalculus.toCanonicalRestrictedPVMSpectralTheorem
    hSelf hSupport

/-- Exact-gap PVM support endpoint generated from ball functional calculus. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_ball_functionalCalculus
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M)
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
      ((B.toCanonicalRestrictedPVMSpectralTheorem hSelf hSupport).toCanonicalPVMOpenSupportBridge
        hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact
    explicit_wightman_os_exact_gap_pvm_open_support_of_local_functionalCalculus
      M B.toLocalFunctionalCalculus hSelf D hGap hExactSpectrum hSupport

end

end MathlibAnalytic
end MGAP4D
