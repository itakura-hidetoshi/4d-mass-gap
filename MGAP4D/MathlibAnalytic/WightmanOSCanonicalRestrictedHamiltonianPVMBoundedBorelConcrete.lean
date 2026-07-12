import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMLocalFunctionalCalculus
import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelAlgebra
import MGAP4D.MathlibAnalytic.WightmanOSPVMDisjointCompositionDerived
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Every ambient spectral projection preserves the vacuum-orthogonal Hilbert
sector.  The proof uses only the existing PVM projection laws and the fact that
the vacuum is the zero-energy spectral vector. -/
theorem ExplicitWightmanOSReconstructedModel.spectralPVM_projection_mem_vacuumOrthogonal
    (M : ExplicitWightmanOSReconstructedModel)
    (s : Set ℝ) {ψ : M.H} (hψ : ψ ∈ M.vacuumOrthogonal) :
    M.spectralPVM.projection s ψ ∈ M.vacuumOrthogonal := by
  rw [explicit_wightman_os_mem_vacuumOrthogonal_iff]
  let hCompositionZero :=
    orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      M.spectralPVM
  by_cases h0 : 0 ∈ s
  · let t : Set ℝ := s \ ({0} : Set ℝ)
    have hDisjoint : Disjoint ({0} : Set ℝ) t := by
      rw [Set.disjoint_left]
      intro x hx0 hxt
      exact hxt.2 hx0
    have hUnion : ({0} : Set ℝ) ∪ t = s := by
      ext x
      by_cases hx : x = 0 <;> simp [t, hx, h0]
    have htVacuum : M.spectralPVM.projection t M.vacuum = 0 := by
      have h := hCompositionZero t ({0} : Set ℝ) hDisjoint.symm M.vacuum
      rw [M.vacuumSpectralProjection] at h
      exact h
    have hsVacuum : M.spectralPVM.projection s M.vacuum = M.vacuum := by
      have hAdd :=
        M.spectralPVM.disjoint_additive ({0} : Set ℝ) t hDisjoint M.vacuum
      simpa [hUnion, M.vacuumSpectralProjection, htVacuum] using hAdd
    calc
      inner ℝ M.vacuum (M.spectralPVM.projection s ψ) =
          inner ℝ (M.spectralPVM.projection s M.vacuum) ψ :=
        (M.spectralPVM.selfAdjoint s M.vacuum ψ).symm
      _ = inner ℝ M.vacuum ψ := by rw [hsVacuum]
      _ = 0 :=
        (explicit_wightman_os_mem_vacuumOrthogonal_iff M ψ).mp hψ
  · have hDisjoint : Disjoint s ({0} : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hxs hx0
      have hx : x = 0 := by simpa using hx0
      subst x
      exact h0 hxs
    have hsVacuum : M.spectralPVM.projection s M.vacuum = 0 := by
      have h := hCompositionZero s ({0} : Set ℝ) hDisjoint M.vacuum
      rw [M.vacuumSpectralProjection] at h
      exact h
    calc
      inner ℝ M.vacuum (M.spectralPVM.projection s ψ) =
          inner ℝ (M.spectralPVM.projection s M.vacuum) ψ :=
        (M.spectralPVM.selfAdjoint s M.vacuum ψ).symm
      _ = 0 := by rw [hsVacuum]; simp

/-- The ambient Hamiltonian PVM restricted to the complete physical sector
`Ω⊥`. -/
noncomputable def ExplicitWightmanOSReconstructedModel.vacuumOrthogonalSpectralPVM
    (M : ExplicitWightmanOSReconstructedModel) :
    OrthogonalProjectionValuedSetFunction M.VacuumOrthogonalHilbert where
  projection := fun s =>
    (M.spectralPVM.projection s).restrict
      (p := M.vacuumOrthogonal) (q := M.vacuumOrthogonal)
      (fun x hx => M.spectralPVM_projection_mem_vacuumOrthogonal s hx)
  empty_apply := by
    intro x
    apply Subtype.ext
    change M.spectralPVM.projection ∅ (x : M.H) = (0 : M.H)
    exact M.spectralPVM.empty_apply (x : M.H)
  univ_apply := by
    intro x
    apply Subtype.ext
    change M.spectralPVM.projection Set.univ (x : M.H) = (x : M.H)
    exact M.spectralPVM.univ_apply (x : M.H)
  idempotent := by
    intro s x
    apply Subtype.ext
    change
      M.spectralPVM.projection s
          (M.spectralPVM.projection s (x : M.H)) =
        M.spectralPVM.projection s (x : M.H)
    exact M.spectralPVM.idempotent s (x : M.H)
  selfAdjoint := by
    intro s x y
    change
      inner ℝ (M.spectralPVM.projection s (x : M.H)) (y : M.H) =
        inner ℝ (x : M.H) (M.spectralPVM.projection s (y : M.H))
    exact M.spectralPVM.selfAdjoint s (x : M.H) (y : M.H)
  disjoint_additive := by
    intro s t hst x
    apply Subtype.ext
    change
      M.spectralPVM.projection (s ∪ t) (x : M.H) =
        M.spectralPVM.projection s (x : M.H) +
          M.spectralPVM.projection t (x : M.H)
    exact M.spectralPVM.disjoint_additive s t hst (x : M.H)

/-- Forget the physical-layer bounded-Borel wrapper into the lightweight
standalone PVM integration wrapper. -/
def pvmBoundedBorelOfExplicit
    (f : ExplicitBoundedBorelRealFunction) : PVMBoundedBorelRealFunction where
  toFun := f.toFun
  measurable_toFun := f.measurable_toFun
  bounded_toFun := f.bounded_toFun

@[simp] theorem pvmBoundedBorelOfExplicit_one :
    pvmBoundedBorelOfExplicit explicitBoundedBorelOne = pvmBoundedBorelOne := by
  apply PVMBoundedBorelRealFunction.ext
  rfl

@[simp] theorem pvmBoundedBorelOfExplicit_sub
    (f g : ExplicitBoundedBorelRealFunction) :
    pvmBoundedBorelOfExplicit (explicitBoundedBorelSub f g) =
      pvmBoundedBorelSub (pvmBoundedBorelOfExplicit f)
        (pvmBoundedBorelOfExplicit g) := by
  apply PVMBoundedBorelRealFunction.ext
  rfl

@[simp] theorem pvmBoundedBorelOfExplicit_indicator
    (s : Set ℝ) (hs : MeasurableSet s) :
    pvmBoundedBorelOfExplicit (explicitBoundedBorelIndicator s hs) =
      pvmBoundedBorelIndicator s hs := by
  apply PVMBoundedBorelRealFunction.ext
  rfl

/-- The actual bounded Borel PVM integral on the canonical vacuum-orthogonal
Hilbert sector, obtained by the simple-function completion constructed in the
standalone PVM layer. -/
noncomputable def ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
    (M : ExplicitWightmanOSReconstructedModel)
    (f : ExplicitBoundedBorelRealFunction) :
    M.VacuumOrthogonalHilbert →L[ℝ] M.VacuumOrthogonalHilbert :=
  pvmBoundedBorelSpectralIntegralOperator M.vacuumOrthogonalSpectralPVM
    (pvmBoundedBorelOfExplicit f)

/-- The canonical restricted bounded Borel integral sends one to the identity. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one
    (M : ExplicitWightmanOSReconstructedModel) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        explicitBoundedBorelOne =
      ContinuousLinearMap.id ℝ M.VacuumOrthogonalHilbert := by
  unfold canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
  rw [pvmBoundedBorelOfExplicit_one,
    pvmBoundedBorelSpectralIntegralOperator_one]

@[simp] theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one_apply
    (M : ExplicitWightmanOSReconstructedModel)
    (ψ : M.VacuumOrthogonalHilbert) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        explicitBoundedBorelOne ψ = ψ := by
  rw [M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one]
  rfl

/-- The canonical restricted bounded Borel integral preserves subtraction. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_sub
    (M : ExplicitWightmanOSReconstructedModel)
    (f g : ExplicitBoundedBorelRealFunction) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        (explicitBoundedBorelSub f g) =
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f -
        M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral g := by
  unfold canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
  rw [pvmBoundedBorelOfExplicit_sub,
    pvmBoundedBorelSpectralIntegralOperator_sub]

/-- The canonical restricted bounded Borel integral of an indicator is the
ambient spectral projection after inclusion into the physical Hilbert space. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_indicator
    (M : ExplicitWightmanOSReconstructedModel)
    (s : Set ℝ) (hs : MeasurableSet s)
    (ψ : M.VacuumOrthogonalHilbert) :
    ((M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
          (explicitBoundedBorelIndicator s hs) ψ :
        M.VacuumOrthogonalHilbert) : M.H) =
      M.spectralPVM.projection s (ψ : M.H) := by
  unfold canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
  rw [pvmBoundedBorelOfExplicit_indicator,
    pvmBoundedBorelSpectralIntegralOperator_indicator]
  rfl

/-- The single remaining compatibility between the canonical Hamiltonian and its
PVM functional calculus: multiplication by the shifted coordinate realizes the
restricted Hamiltonian graph. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph
    (M : ExplicitWightmanOSReconstructedModel) where
  shiftedCoordinate_graph :
    ∀ (E : ℝ) (f g : ExplicitBoundedBorelRealFunction),
      (∀ t : ℝ, g.toFun t = (t - E) * f.toFun t) →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
          (x : M.VacuumOrthogonalHilbert) =
              M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f ψ ∧
            M.canonicalVacuumOrthogonalHamiltonian.realShift E x =
              M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral g ψ

/-- Concrete constructor for the physical bounded Borel spectral-integral
package.  The one, subtraction, and indicator fields are discharged by the
actual PVM integration construction; only the Hamiltonian graph compatibility
remains as input. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph.toBoundedBorelSpectralIntegral
    {M : ExplicitWightmanOSReconstructedModel}
    (G : ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph M) :
    ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral M :=
  { spectralIntegral :=
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
    spectralIntegral_one :=
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one_apply
    spectralIntegral_sub := by
      intro f g ψ
      exact congrArg (fun T :
          M.VacuumOrthogonalHilbert →L[ℝ] M.VacuumOrthogonalHilbert => T ψ)
        (M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_sub f g)
    spectralIntegral_indicator :=
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_indicator
    shiftedCoordinate_graph := G.shiftedCoordinate_graph }

end

end MathlibAnalytic
end MGAP4D
