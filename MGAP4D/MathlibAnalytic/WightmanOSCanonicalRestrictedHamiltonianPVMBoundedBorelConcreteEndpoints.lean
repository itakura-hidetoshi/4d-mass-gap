import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMBoundedBorelConcrete

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The reciprocal of the shifted coordinate, truncated to zero on a positive
ball around its singularity, as a lightweight bounded Borel function. -/
def pvmSpectralBallTruncatedReciprocal
    (E ε : ℝ) (hε : 0 < ε) : PVMBoundedBorelRealFunction := by
  classical
  exact
    { toFun := fun t =>
        if dist t E < ε then 0 else (t - E)⁻¹
      measurable_toFun := by
        change Measurable fun t : ℝ =>
          if t ∈ Metric.ball E ε then 0 else (t - E)⁻¹
        exact Measurable.ite Metric.isOpen_ball.measurableSet
          measurable_const ((measurable_id.sub measurable_const).inv)
      bounded_toFun := by
        refine ⟨ε⁻¹, ?_⟩
        intro t
        by_cases hdist : dist t E < ε
        · have hInvNonneg : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
          simpa [hdist] using hInvNonneg
        · have hdistLower : ε ≤ dist t E := le_of_not_gt hdist
          have habs : ε ≤ |t - E| := by
            simpa [Real.dist_eq] using hdistLower
          have hReciprocal : 1 / |t - E| ≤ 1 / ε :=
            one_div_le_one_div_of_le hε habs
          simpa [hdist, Real.norm_eq_abs, abs_inv, one_div] using
            hReciprocal }

/-- The shifted coordinate cancels the truncated reciprocal away from the
removed ball and both sides vanish on the ball. -/
theorem pvmBoundedBorel_one_sub_ballIndicator_eq_shift_mul_truncatedReciprocal
    {E ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (pvmBoundedBorelSub pvmBoundedBorelOne
      (pvmBoundedBorelIndicator (Metric.ball E ε)
        Metric.isOpen_ball.measurableSet)).toFun t =
      (t - E) * (pvmSpectralBallTruncatedReciprocal E ε hε).toFun t := by
  classical
  by_cases ht : t ∈ Metric.ball E ε
  · have hdist : dist t E < ε := Metric.mem_ball.mp ht
    simp [pvmBoundedBorelSub, pvmBoundedBorelOne,
      pvmBoundedBorelIndicator, pvmSpectralBallTruncatedReciprocal,
      ht, hdist]
  · have hdist : ¬dist t E < ε := by
      simpa only [Metric.mem_ball] using ht
    have htE : t ≠ E := by
      intro h
      subst t
      exact ht (Metric.mem_ball_self hε)
    have hsub : t - E ≠ 0 := sub_ne_zero.mpr htE
    simp [pvmBoundedBorelSub, pvmBoundedBorelOne,
      pvmBoundedBorelIndicator, pvmSpectralBallTruncatedReciprocal,
      ht, hdist, hsub]

/-- The actual completed bounded Borel PVM integral constructs a preimage of a
vector whose spectral projection vanishes on a positive ball. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMCompletedBoundedBorelSpectralIntegral.ballVanish_has_preimage
    {M : ExplicitWightmanOSReconstructedModel}
    (F :
      ExplicitWightmanOSCanonicalRestrictedPVMCompletedBoundedBorelSpectralIntegral M)
    (E ε : ℝ) (hε : 0 < ε)
    (ψ : M.VacuumOrthogonalHilbert)
    (hZero :
      M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0) :
    ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
      M.canonicalVacuumOrthogonalHamiltonian x -
          E • (x : M.VacuumOrthogonalHilbert) = ψ := by
  let f := pvmSpectralBallTruncatedReciprocal E ε hε
  let i := pvmBoundedBorelIndicator (Metric.ball E ε)
    Metric.isOpen_ball.measurableSet
  let g := pvmBoundedBorelSub pvmBoundedBorelOne i
  have hMul : ∀ t : ℝ, g.toFun t = (t - E) * f.toFun t := by
    intro t
    exact
      pvmBoundedBorel_one_sub_ballIndicator_eq_shift_mul_truncatedReciprocal
        hε t
  obtain ⟨x, _hxIntegral, hShift⟩ :=
    F.shiftedCoordinate_graph E f g hMul ψ
  refine ⟨x, ?_⟩
  have hIndicatorZero : F.spectralIntegral i ψ = 0 := by
    apply Subtype.ext
    change ((F.spectralIntegral i ψ : M.VacuumOrthogonalHilbert) : M.H) = 0
    dsimp [i]
    rw [F.spectralIntegral_indicator]
    exact hZero
  have hIntegralG : F.spectralIntegral g ψ = ψ := by
    calc
      F.spectralIntegral g ψ =
          F.spectralIntegral pvmBoundedBorelOne ψ -
            F.spectralIntegral i ψ := by
              dsimp [g]
              exact F.spectralIntegral_sub pvmBoundedBorelOne i ψ
      _ = ψ - 0 := by
        rw [F.spectralIntegral_one, hIndicatorZero]
      _ = ψ := sub_zero ψ
  exact hShift.trans hIntegralG

/-- The single shifted-coordinate graph compatibility therefore yields the
ball-truncated reciprocal preimage through the theorem-generated completed PVM
integral. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph.ballVanish_has_preimage
    {M : ExplicitWightmanOSReconstructedModel}
    (G : ExplicitWightmanOSCanonicalRestrictedPVMShiftedCoordinateGraph M)
    (E ε : ℝ) (hε : 0 < ε)
    (ψ : M.VacuumOrthogonalHilbert)
    (hZero :
      M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0) :
    ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
      M.canonicalVacuumOrthogonalHamiltonian x -
          E • (x : M.VacuumOrthogonalHilbert) = ψ := by
  exact G.toCompletedBoundedBorelSpectralIntegral.ballVanish_has_preimage
    E ε hε ψ hZero

end

end MathlibAnalytic
end MGAP4D
