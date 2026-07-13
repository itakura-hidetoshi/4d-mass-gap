import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHamiltonianGenerator
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMCoordinateGraph
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

/-- A self-adjoint partially defined operator is maximal among formally symmetric
extensions. -/
theorem linearPMap_eq_of_le_of_isSelfAdjoint_of_isFormalAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {A B : H →ₗ.[ℝ] H}
    (hAB : A ≤ B)
    (hA : IsSelfAdjoint A)
    (hB : B.IsFormalAdjoint B) :
    A = B := by
  apply le_antisymm hAB
  have hABFormal : A.IsFormalAdjoint B := by
    intro x y
    let xB : B.domain := ⟨(x : H), hAB.1 x.property⟩
    have hAx : A x = B xB := hAB.2 rfl
    calc
      inner ℝ (A x) (y : H) = inner ℝ (B xB) (y : H) := by rw [hAx]
      _ = inner ℝ (xB : H) (B y) := hB xB y
      _ = inner ℝ (x : H) (B y) := rfl
  have hBA : B ≤ A.adjoint :=
    hABFormal.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hBA
  exact hBA

namespace EuclideanYangMillsOSPhysicalTimeTranslation

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
variable {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}

/-- The positive-time Hamiltonian difference quotient associated with the
physical Euclidean semigroup. -/
def rightHamiltonianDifferenceQuotient
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (ψ : M.observables.PhysicalHilbert) (t : ℝ) :
    M.observables.PhysicalHilbert :=
  t⁻¹ • (ψ - T.operator t ψ)

/-- A vector has right-Hamiltonian value `η` when the positive-time Hamiltonian
difference quotient converges to `η` at the semigroup origin. -/
def HasRightHamiltonianValue
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (ψ η : M.observables.PhysicalHilbert) : Prop :=
  Tendsto (fun t : ℝ => T.rightHamiltonianDifferenceQuotient ψ t)
    (nhdsWithin 0 (Ioi 0)) (nhds η)

/-- Right-Hamiltonian values are unique. -/
theorem hasRightHamiltonianValue_unique
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    {ψ η ζ : M.observables.PhysicalHilbert}
    (hη : T.HasRightHamiltonianValue ψ η)
    (hζ : T.HasRightHamiltonianValue ψ ζ) :
    η = ζ :=
  tendsto_nhds_unique hη hζ

@[simp] theorem rightHamiltonianDifferenceQuotient_zero
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) (t : ℝ) :
    T.rightHamiltonianDifferenceQuotient 0 t = 0 := by
  simp [rightHamiltonianDifferenceQuotient]

@[simp] theorem rightHamiltonianDifferenceQuotient_add
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (ψ φ : M.observables.PhysicalHilbert) (t : ℝ) :
    T.rightHamiltonianDifferenceQuotient (ψ + φ) t =
      T.rightHamiltonianDifferenceQuotient ψ t +
        T.rightHamiltonianDifferenceQuotient φ t := by
  simp only [rightHamiltonianDifferenceQuotient, map_add]
  module

@[simp] theorem rightHamiltonianDifferenceQuotient_smul
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (c : ℝ) (ψ : M.observables.PhysicalHilbert) (t : ℝ) :
    T.rightHamiltonianDifferenceQuotient (c • ψ) t =
      c • T.rightHamiltonianDifferenceQuotient ψ t := by
  simp only [rightHamiltonianDifferenceQuotient, map_smul]
  module

/-- The vectors admitting a positive-time Hamiltonian derivative form a real
linear subspace. -/
noncomputable def rightHamiltonianDomain
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    Submodule ℝ M.observables.PhysicalHilbert where
  carrier := {ψ | ∃ η, T.HasRightHamiltonianValue ψ η}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simpa only [HasRightHamiltonianValue,
      rightHamiltonianDifferenceQuotient_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : M.observables.PhysicalHilbert))
          (nhdsWithin 0 (Ioi 0)) (nhds 0))
  add_mem' := by
    rintro ψ φ ⟨η, hη⟩ ⟨ζ, hζ⟩
    refine ⟨η + ζ, ?_⟩
    unfold HasRightHamiltonianValue at hη hζ ⊢
    simpa only [rightHamiltonianDifferenceQuotient_add] using hη.add hζ
  smul_mem' := by
    rintro c ψ ⟨η, hη⟩
    refine ⟨c • η, ?_⟩
    unfold HasRightHamiltonianValue at hη ⊢
    simpa only [rightHamiltonianDifferenceQuotient_smul] using
      (tendsto_const_nhds.smul hη :
        Tendsto
          (fun t : ℝ => c • T.rightHamiltonianDifferenceQuotient ψ t)
          (nhdsWithin 0 (Ioi 0)) (nhds (c • η)))

/-- The canonical positive-time Hamiltonian on its derivative domain. -/
noncomputable def rightHamiltonian
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    T.rightHamiltonianDomain →ₗ[ℝ] M.observables.PhysicalHilbert where
  toFun := fun ψ => Classical.choose ψ.property
  map_add' := by
    intro ψ φ
    apply T.hasRightHamiltonianValue_unique
      (Classical.choose_spec (ψ + φ).property)
    have hψ := Classical.choose_spec ψ.property
    have hφ := Classical.choose_spec φ.property
    unfold HasRightHamiltonianValue at hψ hφ ⊢
    simpa [rightHamiltonianDifferenceQuotient_add] using hψ.add hφ
  map_smul' := by
    intro c ψ
    apply T.hasRightHamiltonianValue_unique
      (Classical.choose_spec (c • ψ).property)
    have hψ := Classical.choose_spec ψ.property
    unfold HasRightHamiltonianValue at hψ ⊢
    simpa [rightHamiltonianDifferenceQuotient_smul] using
      (tendsto_const_nhds.smul hψ :
        Tendsto
          (fun t : ℝ => c • T.rightHamiltonianDifferenceQuotient
            (ψ : M.observables.PhysicalHilbert) t)
          (nhdsWithin 0 (Ioi 0))
          (nhds (c • Classical.choose ψ.property)))

/-- The selected positive-time Hamiltonian has its defining derivative value. -/
theorem rightHamiltonian_hasRightHamiltonianValue
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (ψ : T.rightHamiltonianDomain) :
    T.HasRightHamiltonianValue ψ (T.rightHamiltonian ψ) :=
  Classical.choose_spec ψ.property

/-- The positive-time Hamiltonian represented as a Mathlib `LinearPMap`. -/
noncomputable def rightHamiltonianLinearPMap
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    M.observables.PhysicalHilbert →ₗ.[ℝ]
      M.observables.PhysicalHilbert where
  domain := T.rightHamiltonianDomain
  toFun := T.rightHamiltonian

/-- Inner-product symmetry of the physical Euclidean-time semigroup. -/
def IsInnerSymmetric
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop :=
  ∀ (t : ℝ) (ψ φ : M.observables.PhysicalHilbert),
    inner ℝ (T.operator t ψ) φ = inner ℝ ψ (T.operator t φ)

/-- Semigroup symmetry passes to every Hamiltonian difference quotient. -/
theorem rightHamiltonianDifferenceQuotient_inner_eq_of_innerSymmetric
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (hSymmetric : T.IsInnerSymmetric)
    (t : ℝ) (ψ φ : M.observables.PhysicalHilbert) :
    inner ℝ (T.rightHamiltonianDifferenceQuotient ψ t) φ =
      inner ℝ ψ (T.rightHamiltonianDifferenceQuotient φ t) := by
  simp only [rightHamiltonianDifferenceQuotient, inner_smul_left,
    inner_sub_left, inner_smul_right, inner_sub_right]
  rw [hSymmetric t ψ φ]
  simp

/-- The positive-time Hamiltonian is formally symmetric whenever the physical
semigroup is inner-product symmetric. -/
theorem rightHamiltonianLinearPMap_isFormalAdjoint_of_innerSymmetric
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (hSymmetric : T.IsInnerSymmetric) :
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
  have hfunctions :
      (fun t : ℝ =>
        inner ℝ
          (T.rightHamiltonianDifferenceQuotient
            (ψ : M.observables.PhysicalHilbert) t)
          (φ : M.observables.PhysicalHilbert)) =
        fun t : ℝ =>
          inner ℝ (ψ : M.observables.PhysicalHilbert)
            (T.rightHamiltonianDifferenceQuotient
              (φ : M.observables.PhysicalHilbert) t) := by
    funext t
    exact T.rightHamiltonianDifferenceQuotient_inner_eq_of_innerSymmetric
      hSymmetric t ψ φ
  rw [hfunctions] at hleft
  exact tendsto_nhds_unique hleft hright

end EuclideanYangMillsOSPhysicalTimeTranslation

namespace EuclideanYangMillsOSPhysicalHamiltonianGenerator

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
variable {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
variable {T : EuclideanYangMillsOSPhysicalTimeTranslation M}

/-- The displayed Hamiltonian domain is contained in the canonical positive-time
derivative domain, with the same Hamiltonian value. -/
theorem hasRightHamiltonianValue
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (x : M.hamiltonian.domain) :
    T.HasRightHamiltonianValue
      (x : M.observables.PhysicalHilbert) (M.hamiltonian x) := by
  unfold EuclideanYangMillsOSPhysicalTimeTranslation.HasRightHamiltonianValue
  have hneg := (G.generatorLimit x).neg
  have hfunctions :
      (fun t : ℝ =>
        T.rightHamiltonianDifferenceQuotient
          (x : M.observables.PhysicalHilbert) t) =
        fun t : ℝ =>
          -(t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert))) := by
    funext t
    simp only [EuclideanYangMillsOSPhysicalTimeTranslation.rightHamiltonianDifferenceQuotient]
    module
  rw [hfunctions]
  simpa using hneg

/-- The reconstructed self-adjoint Hamiltonian is contained in the positive-time
Hamiltonian selected from semigroup derivatives. -/
theorem hamiltonian_le_rightHamiltonianLinearPMap
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T) :
    M.hamiltonian ≤ T.rightHamiltonianLinearPMap := by
  refine ⟨?_, ?_⟩
  · intro ψ hψ
    exact ⟨M.hamiltonian ⟨ψ, hψ⟩,
      G.hasRightHamiltonianValue ⟨ψ, hψ⟩⟩
  · intro x y hxy
    apply T.hasRightHamiltonianValue_unique
    · simpa only [hxy] using G.hasRightHamiltonianValue x
    · exact T.rightHamiltonian_hasRightHamiltonianValue y

/-- By self-adjoint maximality, a symmetric semigroup right-Hamiltonian extending
the reconstructed self-adjoint Hamiltonian is exactly that Hamiltonian. -/
theorem hamiltonian_eq_rightHamiltonianLinearPMap
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hSymmetric : T.IsInnerSymmetric) :
    M.hamiltonian = T.rightHamiltonianLinearPMap := by
  exact linearPMap_eq_of_le_of_isSelfAdjoint_of_isFormalAdjoint
    G.hamiltonian_le_rightHamiltonianLinearPMap
    M.hamiltonianSelfAdjoint
    (T.rightHamiltonianLinearPMap_isFormalAdjoint_of_innerSymmetric hSymmetric)

/-- Every positive-time Hamiltonian derivative value is therefore an actual
value of the reconstructed Hamiltonian. -/
theorem exists_hamiltonianDomain_eq_of_hasRightHamiltonianValue
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hSymmetric : T.IsInnerSymmetric)
    {ψ η : M.observables.PhysicalHilbert}
    (hValue : T.HasRightHamiltonianValue ψ η) :
    ∃ x : M.hamiltonian.domain,
      (x : M.observables.PhysicalHilbert) = ψ ∧ M.hamiltonian x = η := by
  have hEq := G.hamiltonian_eq_rightHamiltonianLinearPMap hSymmetric
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

/-- The spectral integral has the derivative predicted by multiplication with
the spectral coordinate. -/
structure EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  spectralIntegral_hasRightHamiltonianValue :
    ∀ (f h : PVMBoundedBorelRealFunction),
      (∀ energy : ℝ, h.toFun energy = energy * f.toFun energy) →
      ∀ ψ : M.toExplicitModel.VacuumOrthogonalHilbert,
        T.HasRightHamiltonianValue
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              f ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H))
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              h ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H))

/-- Symmetric semigroup maximality and the spectral derivative formula construct
the full canonical restricted PVM coordinate graph. -/
noncomputable def EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue.toCoordinateGraph
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (V : EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue T)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (hSymmetric : T.IsInnerSymmetric) :
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
      G.exists_hamiltonianDomain_eq_of_hasRightHamiltonianValue
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

end

end MathlibAnalytic
end MGAP4D
