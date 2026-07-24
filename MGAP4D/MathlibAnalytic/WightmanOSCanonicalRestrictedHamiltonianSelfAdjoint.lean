import MGAP4D.MathlibAnalytic.WightmanOSVacuumHamiltonianProjectionReduction
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

/-- Data identifying a partial operator on a closed Hilbert subspace with the
restriction of an ambient partial operator, together with a reducing orthogonal
projection. -/
structure RealLinearPMapOrthogonalRestrictionData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (B : K →ₗ.[ℝ] K) : Prop where
  domain_iff :
    ∀ x : K, x ∈ B.domain ↔ (x : H) ∈ A.domain
  apply_coe :
    ∀ x : B.domain,
      ((B x : K) : H) =
        A ⟨((x : K) : H), (domain_iff (x : K)).mp x.property⟩
  projection_mem_domain :
    ∀ x : A.domain, K.starProjection (x : H) ∈ A.domain
  projection_commutes :
    ∀ x : A.domain,
      A ⟨K.starProjection (x : H), projection_mem_domain x⟩ =
        K.starProjection (A x)

/-- A point in the restricted domain obtained by orthogonally projecting an
ambient-domain point. -/
def RealLinearPMapOrthogonalRestrictionData.projectedDomainPoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : H →ₗ.[ℝ] H} {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    {B : K →ₗ.[ℝ] K}
    (D : RealLinearPMapOrthogonalRestrictionData A K B)
    (x : A.domain) : B.domain :=
  ⟨⟨K.starProjection (x : H), K.starProjection_apply_mem (x : H)⟩,
    (D.domain_iff _).2 (D.projection_mem_domain x)⟩

@[simp]
theorem RealLinearPMapOrthogonalRestrictionData.projectedDomainPoint_coe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : H →ₗ.[ℝ] H} {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    {B : K →ₗ.[ℝ] K}
    (D : RealLinearPMapOrthogonalRestrictionData A K B)
    (x : A.domain) :
    (((D.projectedDomainPoint x : B.domain) : K) : H) =
      K.starProjection (x : H) :=
  rfl

theorem RealLinearPMapOrthogonalRestrictionData.apply_projectedDomainPoint_coe
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : H →ₗ.[ℝ] H} {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    {B : K →ₗ.[ℝ] K}
    (D : RealLinearPMapOrthogonalRestrictionData A K B)
    (x : A.domain) :
    ((B (D.projectedDomainPoint x) : K) : H) =
      K.starProjection (A x) := by
  calc
    ((B (D.projectedDomainPoint x) : K) : H) =
        A ⟨K.starProjection (x : H), D.projection_mem_domain x⟩ := by
      rw [D.apply_coe]
      congr 1
    _ = K.starProjection (A x) := D.projection_commutes x

theorem real_inner_coe_starProjection_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (u : K) (x : H) :
    inner ℝ (u : H) x = inner ℝ (u : H) (K.starProjection x) := by
  have hx : K.starProjection x + (x - K.starProjection x) = x := by
    rw [add_comm, sub_add_cancel]
  calc
    inner ℝ (u : H) x =
        inner ℝ (u : H)
          (K.starProjection x + (x - K.starProjection x)) := by rw [hx]
    _ = inner ℝ (u : H) (K.starProjection x) +
        inner ℝ (u : H) (x - K.starProjection x) := by
      rw [inner_add_right]
    _ = inner ℝ (u : H) (K.starProjection x) := by
      rw [Submodule.inner_right_of_mem_orthogonal u.property
        (K.sub_starProjection_mem_orthogonal x), add_zero]

theorem RealLinearPMapOrthogonalRestrictionData.dense_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : H →ₗ.[ℝ] H} {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    {B : K →ₗ.[ℝ] K}
    (D : RealLinearPMapOrthogonalRestrictionData A K B)
    (hDense : Dense (A.domain : Set H)) :
    Dense (B.domain : Set K) := by
  have hProjectionSurjective : Function.Surjective K.orthogonalProjection := by
    intro y
    refine ⟨(y : H), ?_⟩
    exact K.orthogonalProjection_mem_subspace_eq_self y
  have hProjectedDense :
      DenseRange (fun x : A.domain => K.orthogonalProjection (x : H)) := by
    have hComp := hProjectionSurjective.denseRange.comp
      hDense.denseRange_val K.orthogonalProjection.continuous
    simpa only [Function.comp_apply] using hComp
  intro y
  apply closure_mono ?_ (hProjectedDense y)
  rintro z ⟨x, rfl⟩
  exact (D.projectedDomainPoint x).property

theorem RealLinearPMapOrthogonalRestrictionData.isFormalAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : H →ₗ.[ℝ] H} {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    {B : K →ₗ.[ℝ] K}
    (D : RealLinearPMapOrthogonalRestrictionData A K B)
    (hFormal : A.IsFormalAdjoint A) :
    B.IsFormalAdjoint B := by
  intro x y
  change
    inner ℝ ((B x : K) : H) ((y : K) : H) =
      inner ℝ ((x : K) : H) ((B y : K) : H)
  rw [D.apply_coe, D.apply_coe]
  exact hFormal
    ⟨((x : K) : H), (D.domain_iff (x : K)).mp x.property⟩
    ⟨((y : K) : H), (D.domain_iff (y : K)).mp y.property⟩

theorem RealLinearPMapOrthogonalRestrictionData.isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {A : H →ₗ.[ℝ] H} {K : Submodule ℝ H} [K.HasOrthogonalProjection]
    [CompleteSpace K]
    {B : K →ₗ.[ℝ] K}
    (D : RealLinearPMapOrthogonalRestrictionData A K B)
    (hA : IsSelfAdjoint A) :
    IsSelfAdjoint B := by
  have hDenseA : Dense (A.domain : Set H) := hA.dense_domain
  have hAdjointA : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hFormalA : A.IsFormalAdjoint A := by
    have hFormal := LinearPMap.adjoint_isFormalAdjoint hDenseA
    rw [hAdjointA] at hFormal
    exact hFormal
  have hDenseB : Dense (B.domain : Set K) := D.dense_domain hDenseA
  have hFormalB : B.IsFormalAdjoint B := D.isFormalAdjoint hFormalA
  have hB_le_adjoint : B ≤ B.adjoint := hFormalB.le_adjoint hDenseB
  have hAdjointDomain_le : B.adjoint.domain ≤ B.domain := by
    intro y hy
    let yAdjoint : B.adjoint.domain := ⟨y, hy⟩
    let w : K := B.adjoint yAdjoint
    have hyAmbientAdjoint : (y : H) ∈ A.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨(w : H), ?_⟩
      intro x
      let px : B.domain := D.projectedDomainPoint x
      calc
        inner ℝ (w : H) (x : H) =
            inner ℝ (w : H) (K.starProjection (x : H)) :=
          real_inner_coe_starProjection_right K w (x : H)
        _ = inner ℝ (y : H) ((B px : K) : H) := by
          change inner ℝ (B.adjoint yAdjoint) (px : K) = inner ℝ y (B px)
          exact LinearPMap.adjoint_isFormalAdjoint hDenseB yAdjoint px
        _ = inner ℝ (y : H) (K.starProjection (A x)) := by
          rw [D.apply_projectedDomainPoint_coe]
        _ = inner ℝ (y : H) (A x) :=
          (real_inner_coe_starProjection_right K y (A x)).symm
    have hyAmbientDomain : (y : H) ∈ A.domain := by
      rw [← hAdjointA]
      exact hyAmbientAdjoint
    exact (D.domain_iff y).2 hyAmbientDomain
  have hAdjoint_le_B : B.adjoint ≤ B := by
    refine ⟨hAdjointDomain_le, ?_⟩
    intro x y hxy
    exact (hB_le_adjoint.2 hxy.symm).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAdjoint_le_B hB_le_adjoint

def explicitWightmanOSCanonicalVacuumOrthogonalRestrictionData
    (M : ExplicitWightmanOSReconstructedModel) :
    RealLinearPMapOrthogonalRestrictionData
      M.hamiltonian M.vacuumOrthogonal
        M.canonicalVacuumOrthogonalHamiltonian where
  domain_iff := by intro x; rfl
  apply_coe := by intro x; rfl
  projection_mem_domain := by
    intro x
    exact explicit_wightman_os_vacuumOrthogonal_starProjection_mem_hamiltonianDomain M x
  projection_commutes := by
    intro x
    exact explicit_wightman_os_vacuumOrthogonal_starProjection_commutes_hamiltonian_on_domain M x

theorem explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint
    (M : ExplicitWightmanOSReconstructedModel) :
    IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian := by
  exact
    (explicitWightmanOSCanonicalVacuumOrthogonalRestrictionData M).isSelfAdjoint
      M.hamiltonianSelfAdjoint

theorem explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_dense_domain
    (M : ExplicitWightmanOSReconstructedModel) :
    Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
      Set M.VacuumOrthogonalHilbert)) :=
  (explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint M).dense_domain

theorem explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isClosed
    (M : ExplicitWightmanOSReconstructedModel) :
    LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian :=
  (explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint M).isClosed

/-- Compatibility constructor for the former operator bridge.  Since the
compatibility type is now an abbreviation for pure spectral data, this is the
identity map. -/
def explicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridgeOfSpectrum
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M) :
    ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M :=
  B

structure WightmanOSCanonicalRestrictedHamiltonianSelfAdjointReceipt : Prop where
  generic_restriction_selfAdjoint :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H]
      (A : H →ₗ.[ℝ] H) (K : Submodule ℝ H) [K.HasOrthogonalProjection]
      [CompleteSpace K]
      (B : K →ₗ.[ℝ] K)
      (D : RealLinearPMapOrthogonalRestrictionData A K B),
      IsSelfAdjoint A → IsSelfAdjoint B
  actual_restriction_selfAdjoint :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian
  actual_restriction_dense :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
        Set M.VacuumOrthogonalHilbert))
  actual_restriction_closed :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian
  automatic_bridge :
    ∀ (M : ExplicitWightmanOSReconstructedModel)
      (_B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M),
      IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian
  claim_boundary : True

theorem wightmanOSCanonicalRestrictedHamiltonianSelfAdjointReceipt_proved :
    WightmanOSCanonicalRestrictedHamiltonianSelfAdjointReceipt := by
  exact
    { generic_restriction_selfAdjoint := by
        intro H hNormed hInner hComplete A K hProjection hKComplete B D hA
        exact D.isSelfAdjoint hA
      actual_restriction_selfAdjoint :=
        explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint
      actual_restriction_dense :=
        explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_dense_domain
      actual_restriction_closed :=
        explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isClosed
      automatic_bridge := by
        intro M B
        exact explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint M
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
