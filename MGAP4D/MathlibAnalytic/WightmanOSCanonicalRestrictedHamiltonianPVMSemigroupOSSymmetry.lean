import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMSemigroupGenerator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Filter Topology MeasureTheory
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace EuclideanYangMillsOSPositiveTimeObservableConstruction

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}

/-- Positive-time observables map linearly to their represented states in the
completed OS physical Hilbert space. -/
noncomputable def physicalStateLinearMap
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    P.PositiveTimeObservable →ₗ[ℝ] P.PhysicalHilbert where
  toFun := P.physicalState
  map_add' := by
    intro F G
    simp [EuclideanYangMillsOSPositiveTimeObservableConstruction.physicalState,
      EuclideanYangMillsOSPositiveTimeObservableConstruction.osClass]
  map_smul' := by
    intro r F
    simp [EuclideanYangMillsOSPositiveTimeObservableConstruction.physicalState,
      EuclideanYangMillsOSPositiveTimeObservableConstruction.osClass]

@[simp] theorem physicalStateLinearMap_apply
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) :
    P.physicalStateLinearMap F = P.physicalState F :=
  rfl

/-- Represented positive-time observable states are dense in the completed OS
physical Hilbert space. -/
theorem physicalStateLinearMap_denseRange
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    DenseRange P.physicalStateLinearMap := by
  intro x
  exact closure_mono
    (by
      rintro y ⟨q, rfl⟩
      rcases SeparationQuotient.surjective_mk q with ⟨F, rfl⟩
      refine ⟨F, ?_⟩
      exact P.physicalStateLinearMap_apply F)
    ((os_preHilbert_dense_in_physical P) x)

/-- The completed represented-state inner product is the original OS observable
inner product. -/
@[simp] theorem inner_physicalState_physicalState
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F G : P.PositiveTimeObservable) :
    inner ℝ (P.physicalState F) (P.physicalState G) = inner ℝ F G := by
  change inner ℝ
      ((P.osClass F : UniformSpace.Completion P.OSSeparatedPreHilbert))
      ((P.osClass G : UniformSpace.Completion P.OSSeparatedPreHilbert)) =
    inner ℝ F G
  rw [UniformSpace.Completion.inner_coe]
  change inner ℝ (SeparationQuotient.mk F) (SeparationQuotient.mk G) =
    inner ℝ F G
  exact SeparationQuotient.inner_mk_mk F G

end EuclideanYangMillsOSPositiveTimeObservableConstruction

namespace EuclideanYangMillsOSPhysicalTimeTranslation

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
variable {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}

/-- Inner-product symmetry only on nonnegative Euclidean times.  This is the
precise amount required by the positive-time Hamiltonian derivative. -/
def IsRightInnerSymmetric
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → ∀ ψ φ : M.observables.PhysicalHilbert,
    inner ℝ (T.operator t ψ) φ = inner ℝ ψ (T.operator t φ)

/-- The Euclidean measure exchange identity between time reflection and
nonnegative observable translation. -/
def ReflectionTimeTranslationExchange
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → ∀ F G : M.observables.PositiveTimeObservable,
    (∫ ω,
      M.observables.realization (T.observableTranslate t F)
          (M.observables.timeReflection ω) *
        M.observables.realization G ω
      ∂S.measurePackage.euclideanMeasure) =
    ∫ ω,
      M.observables.realization F (M.observables.timeReflection ω) *
        M.observables.realization (T.observableTranslate t G) ω
      ∂S.measurePackage.euclideanMeasure

/-- The measure-level reflection/time-translation exchange identity is exactly
observable inner-product symmetry. -/
theorem ReflectionTimeTranslationExchange.observable_inner_eq
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hExchange : T.ReflectionTimeTranslationExchange)
    (t : ℝ) (ht : 0 ≤ t)
    (F G : M.observables.PositiveTimeObservable) :
    inner ℝ (T.observableTranslate t F) G =
      inner ℝ F (T.observableTranslate t G) := by
  rw [M.observables.osInner_eq_integral,
    M.observables.osInner_eq_integral]
  exact hExchange t ht F G

/-- OS exchange symmetry on dense represented observable states extends to the
whole completed physical Hilbert space. -/
theorem ReflectionTimeTranslationExchange.toIsRightInnerSymmetric
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (hExchange : T.ReflectionTimeTranslationExchange) :
    T.IsRightInnerSymmetric := by
  intro t ht ψ φ
  refine M.observables.physicalStateLinearMap_denseRange.induction_on₂
    ?_ ?_ ψ φ
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F G
    simp only [M.observables.physicalStateLinearMap_apply]
    rw [T.operator_on_dense_state t F ht,
      T.operator_on_dense_state t G ht,
      M.observables.inner_physicalState_physicalState,
      M.observables.inner_physicalState_physicalState]
    exact hExchange.observable_inner_eq t ht F G

/-- Right-time symmetry passes to the positive-time Hamiltonian difference
quotient on the filter relevant to the generator. -/
theorem rightHamiltonianDifferenceQuotient_inner_eq_of_rightInnerSymmetric
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (hSymmetric : T.IsRightInnerSymmetric)
    (t : ℝ) (ht : 0 ≤ t)
    (ψ φ : M.observables.PhysicalHilbert) :
    inner ℝ (T.rightHamiltonianDifferenceQuotient ψ t) φ =
      inner ℝ ψ (T.rightHamiltonianDifferenceQuotient φ t) := by
  simp only [rightHamiltonianDifferenceQuotient, inner_smul_left,
    inner_sub_left, inner_smul_right, inner_sub_right]
  rw [hSymmetric t ht ψ φ]
  simp

/-- Nonnegative-time symmetry suffices to make the canonical right Hamiltonian
formally symmetric. -/
theorem rightHamiltonianLinearPMap_isFormalAdjoint_of_rightInnerSymmetric
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (hSymmetric : T.IsRightInnerSymmetric) :
    T.rightHamiltonianLinearPMap.IsFormalAdjoint
      T.rightHamiltonianLinearPMap := by
  intro ψ φ
  change
    inner ℝ (T.rightHamiltonian ψ) (φ : M.observables.PhysicalHilbert) =
      inner ℝ (ψ : M.observables.PhysicalHilbert) (T.rightHamiltonian φ)
  have hψ := T.rightHamiltonian_hasRightHamiltonianValue ψ
  have hφ := T.rightHamiltonian_hasRightHamiltonianValue φ
  unfold HasRightHamiltonianValue at hψ hφ
  have hleft :
      Tendsto
        (fun t : ℝ =>
          inner ℝ
            (T.rightHamiltonianDifferenceQuotient
              (ψ : M.observables.PhysicalHilbert) t)
            (φ : M.observables.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ (T.rightHamiltonian ψ)
          (φ : M.observables.PhysicalHilbert))) :=
    hψ.inner tendsto_const_nhds
  have hright :
      Tendsto
        (fun t : ℝ =>
          inner ℝ (ψ : M.observables.PhysicalHilbert)
            (T.rightHamiltonianDifferenceQuotient
              (φ : M.observables.PhysicalHilbert) t))
        (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ (ψ : M.observables.PhysicalHilbert)
          (T.rightHamiltonian φ))) :=
    tendsto_const_nhds.inner hφ
  have hEventually :
      (fun t : ℝ =>
        inner ℝ
          (T.rightHamiltonianDifferenceQuotient
            (ψ : M.observables.PhysicalHilbert) t)
          (φ : M.observables.PhysicalHilbert)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      fun t : ℝ =>
        inner ℝ (ψ : M.observables.PhysicalHilbert)
          (T.rightHamiltonianDifferenceQuotient
            (φ : M.observables.PhysicalHilbert) t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact T.rightHamiltonianDifferenceQuotient_inner_eq_of_rightInnerSymmetric
      hSymmetric t (le_of_lt ht) ψ φ
  exact tendsto_nhds_unique (hleft.congr' hEventually) hright

end EuclideanYangMillsOSPhysicalTimeTranslation

namespace EuclideanYangMillsOSPhysicalHamiltonianGenerator

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
variable {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
variable {T : EuclideanYangMillsOSPhysicalTimeTranslation M}

/-- Self-adjoint maximality identifies the reconstructed Hamiltonian with the
right generator using only nonnegative-time symmetry. -/
theorem hamiltonian_eq_rightHamiltonianLinearPMap_of_rightInnerSymmetric
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hSymmetric : T.IsRightInnerSymmetric) :
    M.hamiltonian = T.rightHamiltonianLinearPMap := by
  exact linearPMap_eq_of_le_of_isSelfAdjoint_of_isFormalAdjoint
    G.hamiltonian_le_rightHamiltonianLinearPMap
    M.hamiltonianSelfAdjoint
    (T.rightHamiltonianLinearPMap_isFormalAdjoint_of_rightInnerSymmetric
      hSymmetric)

/-- Every positive-time Hamiltonian derivative is an actual value of the
reconstructed Hamiltonian under right-time symmetry. -/
theorem exists_hamiltonianDomain_eq_of_hasRightHamiltonianValue_of_rightInnerSymmetric
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hSymmetric : T.IsRightInnerSymmetric)
    {ψ η : M.observables.PhysicalHilbert}
    (hValue : T.HasRightHamiltonianValue ψ η) :
    ∃ x : M.hamiltonian.domain,
      (x : M.observables.PhysicalHilbert) = ψ ∧ M.hamiltonian x = η := by
  have hEq :=
    G.hamiltonian_eq_rightHamiltonianLinearPMap_of_rightInnerSymmetric
      hSymmetric
  have hDomainEq :
      M.hamiltonian.domain = T.rightHamiltonianLinearPMap.domain :=
    congrArg LinearPMap.domain hEq
  have hψRight : ψ ∈ T.rightHamiltonianLinearPMap.domain :=
    ⟨η, hValue⟩
  have hψHamiltonian : ψ ∈ M.hamiltonian.domain := by
    rw [hDomainEq]
    exact hψRight
  let x : M.hamiltonian.domain := ⟨ψ, hψHamiltonian⟩
  let y : T.rightHamiltonianLinearPMap.domain := ⟨ψ, hψRight⟩
  refine ⟨x, rfl, ?_⟩
  have hxy : M.hamiltonian x = T.rightHamiltonianLinearPMap y :=
    G.hamiltonian_le_rightHamiltonianLinearPMap.2 rfl
  calc
    M.hamiltonian x = T.rightHamiltonianLinearPMap y := hxy
    _ = T.rightHamiltonian y := rfl
    _ = η := T.hasRightHamiltonianValue_unique
      (T.rightHamiltonian_hasRightHamiltonianValue y) hValue

end EuclideanYangMillsOSPhysicalHamiltonianGenerator

/-- The spectral derivative and nonnegative semigroup symmetry construct the
canonical restricted PVM coordinate graph. -/
noncomputable def EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue.toCoordinateGraphOfRightInnerSymmetric
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (V : EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue T)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hSymmetric : T.IsRightInnerSymmetric) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel where
  coordinate_graph := by
    intro f h hCoordinate ψ
    let vf : M.toExplicitModel.VacuumOrthogonalHilbert :=
      M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f ψ
    let vh : M.toExplicitModel.VacuumOrthogonalHilbert :=
      M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral h ψ
    have hValue : T.HasRightHamiltonianValue
        ((vf : M.toExplicitModel.VacuumOrthogonalHilbert) : M.toExplicitModel.H)
        ((vh : M.toExplicitModel.VacuumOrthogonalHilbert) : M.toExplicitModel.H) := by
      exact V.spectralIntegral_hasRightHamiltonianValue f h hCoordinate ψ
    obtain ⟨xAmbient, hxAmbient, hHxAmbient⟩ :=
      G.exists_hamiltonianDomain_eq_of_hasRightHamiltonianValue_of_rightInnerSymmetric
        hSymmetric hValue
    have hvDomain :
        ((vf : M.toExplicitModel.VacuumOrthogonalHilbert) : M.toExplicitModel.H) ∈
          M.toExplicitModel.hamiltonian.domain := by
      rw [← hxAmbient]
      exact xAmbient.property
    let x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain :=
      ⟨vf, hvDomain⟩
    refine ⟨x, rfl, ?_⟩
    apply Subtype.ext
    change
      ((M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x :
          M.toExplicitModel.VacuumOrthogonalHilbert) : M.toExplicitModel.H) =
        ((vh : M.toExplicitModel.VacuumOrthogonalHilbert) : M.toExplicitModel.H)
    rw [canonical_vacuum_orthogonal_hamiltonian_apply M.toExplicitModel x]
    have hxPoint :
        M.toExplicitModel.vacuumOrthogonalAmbientDomainPoint x = xAmbient := by
      apply Subtype.ext
      exact hxAmbient.symm
    rw [hxPoint]
    exact hHxAmbient

/-- The Euclidean OS reflection/time-translation exchange identity supplies the
semigroup symmetry input and therefore constructs the full coordinate graph. -/
noncomputable def EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue.toCoordinateGraphOfReflectionTimeTranslationExchange
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (V : EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue T)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hExchange : T.ReflectionTimeTranslationExchange) :
    ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M.toExplicitModel :=
  V.toCoordinateGraphOfRightInnerSymmetric G
    hExchange.toIsRightInnerSymmetric

end

end MathlibAnalytic
end MGAP4D
