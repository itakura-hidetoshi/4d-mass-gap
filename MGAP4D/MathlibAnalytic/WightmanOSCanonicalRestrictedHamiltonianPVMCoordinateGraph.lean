import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMBoundedBorelConcreteEndpoints
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- Pointwise real scalar multiplication in the lightweight bounded-Borel
function space used by the completed PVM integral. -/
def pvmBoundedBorelSMul
    (c : ℝ) (F : PVMBoundedBorelRealFunction) :
    PVMBoundedBorelRealFunction where
  toFun := fun t => c * F.toFun t
  measurable_toFun := measurable_const.mul F.measurable_toFun
  bounded_toFun := by
    obtain ⟨C, hC⟩ := F.bounded_toFun
    refine ⟨‖c‖ * C, ?_⟩
    intro t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg c)

@[simp] theorem pvmBoundedBorelSMul_apply
    (c : ℝ) (F : PVMBoundedBorelRealFunction) (t : ℝ) :
    (pvmBoundedBorelSMul c F).toFun t = c * F.toFun t :=
  rfl

/-- A mapped simple function integrates as the corresponding scalar multiple
of its PVM spectral-integral operator. -/
theorem pvmSimpleFuncSpectralIntegralOperator_smul
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (c : ℝ) (f : SimpleFunc ℝ ℝ) :
    pvmSimpleFuncSpectralIntegralOperator P
        (f.map fun a => c * a) =
      c • pvmSimpleFuncSpectralIntegralOperator P f := by
  have hMap :
      f.map (fun a => c * a) =
        (f.pair f).map (fun p : ℝ × ℝ => c * p.1) := by
    ext t
    rfl
  rw [hMap, ← pvmSimpleFuncPairSpectralIntegralOperator_eq_map]
  calc
    pvmSimpleFuncPairSpectralIntegralOperator P f f
        (fun p : ℝ × ℝ => c * p.1) =
      c • pvmSimpleFuncPairSpectralIntegralOperator P f f Prod.fst := by
        ext x
        simp [pvmSimpleFuncPairSpectralIntegralOperator_apply,
          Finset.smul_sum, mul_smul]
    _ = c • pvmSimpleFuncSpectralIntegralOperator P f := by
      rw [pvmSimpleFuncPairSpectralIntegralOperator_fst_eq]

/-- Scalar multiplication of a uniform simple approximation remains a uniform
simple approximation of the pointwise scalar multiple. -/
noncomputable def explicitBoundedBorelSimpleUniformApproximationSMul
    {F : PVMBoundedBorelRealFunction}
    (c : ℝ)
    (A : ExplicitBoundedBorelSimpleUniformApproximation F) :
    ExplicitBoundedBorelSimpleUniformApproximation
      (pvmBoundedBorelSMul c F) where
  simple := fun n => (A.simple n).map fun a => c * a
  uniform_tendsto := by
    intro ε hε
    by_cases hc : c = 0
    · subst c
      refine ⟨0, ?_⟩
      intro n hn t
      simp [pvmBoundedBorelSMul]
      exact hε
    · have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
      have hεc : 0 < ε / ‖c‖ := div_pos hε hcNorm
      obtain ⟨N, hN⟩ := A.uniform_tendsto (ε / ‖c‖) hεc
      refine ⟨N, ?_⟩
      intro n hn t
      change ‖c * A.simple n t - c * F.toFun t‖ < ε
      rw [← mul_sub, norm_mul]
      calc
        ‖c‖ * ‖A.simple n t - F.toFun t‖ <
            ‖c‖ * (ε / ‖c‖) :=
          mul_lt_mul_of_pos_left (hN n hn t) hcNorm
        _ = ε := by field_simp [ne_of_gt hcNorm]

/-- The completed bounded Borel PVM integral is real-linear under scalar
multiplication. -/
theorem pvmBoundedBorelSpectralIntegralOperator_smul
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (c : ℝ) (F : PVMBoundedBorelRealFunction) :
    pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelSMul c F) =
      c • pvmBoundedBorelSpectralIntegralOperator P F := by
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  let C := explicitBoundedBorelSimpleUniformApproximationSMul c A
  have hTerm (n : ℕ) :
      pvmSimpleFuncSpectralIntegralOperator P (C.simple n) =
        c • pvmSimpleFuncSpectralIntegralOperator P (A.simple n) := by
    dsimp [C, explicitBoundedBorelSimpleUniformApproximationSMul]
    exact pvmSimpleFuncSpectralIntegralOperator_smul P c (A.simple n)
  have hScaled :
      Tendsto
        (fun n => pvmSimpleFuncSpectralIntegralOperator P (C.simple n))
        atTop (𝓝 (c • A.completedOperator P)) := by
    have hcT : Tendsto (fun _ : ℕ => (c : ℝ)) atTop (𝓝 c) :=
      tendsto_const_nhds
    have h := hcT.smul (A.tendsto_completedOperator P)
    simpa only [hTerm] using h
  have hA :
      A.completedOperator P =
        pvmBoundedBorelSpectralIntegralOperator P F :=
    A.completedOperator_eq_canonical P
  have hTarget :
      Tendsto
        (fun n => pvmSimpleFuncSpectralIntegralOperator P (C.simple n))
        atTop
        (𝓝 (c • pvmBoundedBorelSpectralIntegralOperator P F)) := by
    simpa only [hA] using hScaled
  have hCompleted :
      C.completedOperator P =
        c • pvmBoundedBorelSpectralIntegralOperator P F :=
    tendsto_nhds_unique (C.tendsto_completedOperator P) hTarget
  calc
    pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelSMul c F) = C.completedOperator P :=
      (C.completedOperator_eq_canonical P).symm
    _ = c • pvmBoundedBorelSpectralIntegralOperator P F := hCompleted

/-- Scalar linearity specialized to the actual completed PVM integral on the
vacuum-orthogonal Hilbert sector. -/
theorem ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_smul
    (M : ExplicitWightmanOSReconstructedModel)
    (c : ℝ) (F : PVMBoundedBorelRealFunction) :
    M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
        (pvmBoundedBorelSMul c F) =
      c • M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral F := by
  exact pvmBoundedBorelSpectralIntegralOperator_smul
    M.vacuumOrthogonalSpectralPVM c F

/-- The primitive Hamiltonian/PVM graph compatibility: multiplication by the
unshifted spectral coordinate `t` realizes the canonical restricted
Hamiltonian.  All real shifts will be derived from this one graph law. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph
    (M : ExplicitWightmanOSReconstructedModel) where
  coordinate_graph :
    ∀ (f h : PVMBoundedBorelRealFunction),
      (∀ t : ℝ, h.toFun t = t * f.toFun t) →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
          (x : M.VacuumOrthogonalHilbert) =
              M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f ψ ∧
            M.canonicalVacuumOrthogonalHamiltonian x =
              M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral h ψ

/-- The single unshifted coordinate graph law generates the full
shifted-coordinate graph by scalar linearity and subtraction of completed PVM
integrals. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph.toShiftedCoordinateGraph
    {M : ExplicitWightmanOSReconstructedModel}
    (G : ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M) :
    ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph M where
  shiftedCoordinate_graph := by
    intro E f g hg ψ
    let ef := pvmBoundedBorelSMul (-E) f
    let h := pvmBoundedBorelSub g ef
    have hh : ∀ t : ℝ, h.toFun t = t * f.toFun t := by
      intro t
      dsimp [h, ef, pvmBoundedBorelSub, pvmBoundedBorelSMul]
      rw [hg t]
      ring
    obtain ⟨x, hx, hHx⟩ := G.coordinate_graph f h hh ψ
    refine ⟨x, hx, ?_⟩
    rw [hHx, hx]
    dsimp [h, ef]
    rw [M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_sub,
      M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral_smul]
    change
      ((M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral g ψ -
          (-E) •
            M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f ψ) -
        E • M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral f ψ) =
        M.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral g ψ
    module

/-- Consequently the unshifted coordinate graph already constructs the
ball-truncated reciprocal preimage used by the resolvent/PVM route. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph.ballVanish_has_preimage
    {M : ExplicitWightmanOSReconstructedModel}
    (G : ExplicitWightmanOSCanonicalRestrictedPVMCoordinateGraph M)
    (E ε : ℝ) (hε : 0 < ε)
    (ψ : M.VacuumOrthogonalHilbert)
    (hZero :
      M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0) :
    ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
      M.canonicalVacuumOrthogonalHamiltonian x -
          E • (x : M.VacuumOrthogonalHilbert) = ψ := by
  exact G.toShiftedCoordinateGraph.ballVanish_has_preimage
    E ε hε ψ hZero

end

end MathlibAnalytic
end MGAP4D
