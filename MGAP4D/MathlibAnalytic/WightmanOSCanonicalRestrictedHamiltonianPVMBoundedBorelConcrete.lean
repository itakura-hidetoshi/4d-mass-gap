import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelAlgebra
import MGAP4D.MathlibAnalytic.WightmanOSPVMDisjointCompositionDerived
import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalHamiltonianInvariance
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Every ambient spectral projection preserves the vacuum-orthogonal Hilbert
sector.  This follows from the PVM projection laws and the zero-energy vacuum
projection, with no Hamiltonian functional-calculus assumption. -/
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
      rw [hUnion, M.vacuumSpectralProjection, htVacuum, add_zero] at hAdd
      exact hAdd
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

/-- The completed bounded Borel PVM integral on the canonical
vacuum-orthogonal Hilbert sector. -/
noncomputable def ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
    (M : ExplicitWightmanOSReconstructedModel)
    (f : PVMBoundedBorelRealFunction) :
    M.VacuumOrthogonalHilbert →L[ℝ] M.VacuumOrthogonalHilbert :=
  pvmBoundedBorelSpectralIntegralOperator M.vacuumOrthogonalSpectralPVM f

/-- The canonical completed integral sends the constant-one function to the
identity operator. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one
    (M : ExplicitWightmanOSReconstructedModel) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral pvmBoundedBorelOne =
      ContinuousLinearMap.id ℝ M.VacuumOrthogonalHilbert := by
  exact pvmBoundedBorelSpectralIntegralOperator_one
    M.vacuumOrthogonalSpectralPVM

@[simp] theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one_apply
    (M : ExplicitWightmanOSReconstructedModel)
    (ψ : M.VacuumOrthogonalHilbert) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        pvmBoundedBorelOne ψ = ψ := by
  rw [M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one]
  rfl

/-- The canonical completed integral preserves subtraction. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_sub
    (M : ExplicitWightmanOSReconstructedModel)
    (f g : PVMBoundedBorelRealFunction) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        (pvmBoundedBorelSub f g) =
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f -
        M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral g := by
  exact pvmBoundedBorelSpectralIntegralOperator_sub
    M.vacuumOrthogonalSpectralPVM f g

/-- The canonical completed integral of a measurable indicator is the ambient
spectral projection after inclusion into the physical Hilbert space. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_indicator
    (M : ExplicitWightmanOSReconstructedModel)
    (s : Set ℝ) (hs : MeasurableSet s)
    (ψ : M.VacuumOrthogonalHilbert) :
    ((M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
          (pvmBoundedBorelIndicator s hs) ψ :
        M.VacuumOrthogonalHilbert) : M.H) =
      M.spectralPVM.projection s (ψ : M.H) := by
  rw [canonicalVacuumOrthogonalBoundedBorelSpectralIntegral,
    pvmBoundedBorelSpectralIntegralOperator_indicator]
  rfl

/-- Completed bounded Borel spectral integration for the canonical restricted
Hamiltonian.  Its algebraic and indicator fields are theorem-generated; the
only operator-level compatibility is the shifted-coordinate graph. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMCompletedBoundedBorelSpectralIntegral
    (M : ExplicitWightmanOSReconstructedModel) where
  spectralIntegral :
    PVMBoundedBorelRealFunction →
      M.VacuumOrthogonalHilbert →L[ℝ] M.VacuumOrthogonalHilbert
  spectralIntegral_one :
    ∀ ψ : M.VacuumOrthogonalHilbert,
      spectralIntegral pvmBoundedBorelOne ψ = ψ
  spectralIntegral_sub :
    ∀ (f g : PVMBoundedBorelRealFunction)
      (ψ : M.VacuumOrthogonalHilbert),
      spectralIntegral (pvmBoundedBorelSub f g) ψ =
        spectralIntegral f ψ - spectralIntegral g ψ
  spectralIntegral_indicator :
    ∀ (s : Set ℝ) (hs : MeasurableSet s)
      (ψ : M.VacuumOrthogonalHilbert),
      ((spectralIntegral (pvmBoundedBorelIndicator s hs) ψ :
          M.VacuumOrthogonalHilbert) : M.H) =
        M.spectralPVM.projection s (ψ : M.H)
  shiftedCoordinate_graph :
    ∀ (E : ℝ) (f g : PVMBoundedBorelRealFunction),
      (∀ t : ℝ, g.toFun t = (t - E) * f.toFun t) →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
          (x : M.VacuumOrthogonalHilbert) = spectralIntegral f ψ ∧
            M.canonicalVacuumOrthogonalHamiltonian.realShift E x =
              spectralIntegral g ψ

/-- The sole residual compatibility needed to attach the actual completed PVM
integral to the canonical restricted Hamiltonian. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph
    (M : ExplicitWightmanOSReconstructedModel) where
  shiftedCoordinate_graph :
    ∀ (E : ℝ) (f g : PVMBoundedBorelRealFunction),
      (∀ t : ℝ, g.toFun t = (t - E) * f.toFun t) →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
          (x : M.VacuumOrthogonalHilbert) =
              M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f ψ ∧
            M.canonicalVacuumOrthogonalHamiltonian.realShift E x =
              M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral g ψ

/-- Concrete constructor: identity, subtraction, and indicator laws come from
simple-function approximation and operator-norm completion; only the shifted
coordinate graph remains as input. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph.toCompletedBoundedBorelSpectralIntegral
    {M : ExplicitWightmanOSReconstructedModel}
    (G : ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph M) :
    ExplicitWightmanOSCanonicalRestrictedPVMCompletedBoundedBorelSpectralIntegral M :=
  { spectralIntegral :=
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
    spectralIntegral_one :=
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_one_apply
    spectralIntegral_sub := by
      intro f g ψ
      simpa using congrArg
        (fun T : M.VacuumOrthogonalHilbert →L[ℝ]
            M.VacuumOrthogonalHilbert => T ψ)
        (M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_sub f g)
    spectralIntegral_indicator :=
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_indicator
    shiftedCoordinate_graph := G.shiftedCoordinate_graph }

end

end MathlibAnalytic
end MGAP4D
