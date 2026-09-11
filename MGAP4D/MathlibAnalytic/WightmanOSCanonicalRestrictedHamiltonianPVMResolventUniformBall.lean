import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMLocalFunctionalCalculus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

noncomputable section

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Surjectivity of a self-adjoint real shift gives its algebraic linear equivalence. -/
noncomputable def realShiftLinearEquivOfSurjective
    (A : H →ₗ.[ℝ] H)
    (hSelf : IsSelfAdjoint A)
    (E : ℝ)
    (hSurjective : Function.Surjective (A.realShift E)) :
    A.domain ≃ₗ[ℝ] H :=
  LinearEquiv.ofBijective (A.realShift E)
    ⟨A.realShift_injective_of_surjective_of_selfAdjoint
      hSelf E hSurjective, hSurjective⟩

/-- The algebraic inverse of a surjective self-adjoint real shift, viewed in the
ambient Hilbert space. -/
noncomputable def realShiftAmbientInverseLinearMap
    (A : H →ₗ.[ℝ] H)
    (hSelf : IsSelfAdjoint A)
    (E : ℝ)
    (hSurjective : Function.Surjective (A.realShift E)) :
    H →ₗ[ℝ] H :=
  A.domain.subtype.comp
    (A.realShiftLinearEquivOfSurjective hSelf E hSurjective).symm.toLinearMap

@[simp] theorem realShiftLinearEquivOfSurjective_apply_symm_apply
    (A : H →ₗ.[ℝ] H)
    (hSelf : IsSelfAdjoint A)
    (E : ℝ)
    (hSurjective : Function.Surjective (A.realShift E))
    (y : H) :
    A.realShift E
        ((A.realShiftLinearEquivOfSurjective hSelf E hSurjective).symm y) = y :=
  (A.realShiftLinearEquivOfSurjective hSelf E hSurjective).apply_symm_apply y

/-- The inverse graph is closed because it is the swapped graph of the closed
self-adjoint shift.  The closed graph theorem therefore upgrades the algebraic
inverse to a continuous linear operator on the ambient Hilbert space. -/
noncomputable def realShiftAmbientInverse
    (A : H →ₗ.[ℝ] H)
    (hSelf : IsSelfAdjoint A)
    (E : ℝ)
    (hSurjective : Function.Surjective (A.realShift E)) :
    H →L[ℝ] H :=
  ContinuousLinearMap.ofSeqClosedGraph
    (g := A.realShiftAmbientInverseLinearMap hSelf E hSurjective) (by
      intro u x y hu hy
      let e := A.realShiftLinearEquivOfSurjective hSelf E hSurjective
      let v : ℕ → A.domain := fun n => e.symm (u n)
      have hv : Tendsto (fun n => ((v n : A.domain) : H)) atTop (𝓝 y) := by
        simpa [realShiftAmbientInverseLinearMap, v, e, Function.comp_def] using hy
      have hShift (n : ℕ) : A.realShift E (v n) = u n := by
        dsimp [v, e]
        exact A.realShiftLinearEquivOfSurjective_apply_symm_apply
          hSelf E hSurjective (u n)
      have hAeq :
          (fun n => A (v n)) =
            fun n => u n + E • ((v n : A.domain) : H) := by
        funext n
        have h := hShift n
        rw [A.realShift_apply] at h
        exact sub_eq_iff_eq_add.mp h
      have hA : Tendsto (fun n => A (v n)) atTop (𝓝 (x + E • y)) := by
        rw [hAeq]
        exact hu.add (tendsto_const_nhds.smul hv)
      have hPair :
          Tendsto (fun n => (((v n : A.domain) : H), A (v n))) atTop
            (𝓝 (y, x + E • y)) :=
        hv.prodMk_nhds hA
      have hLimit : (y, x + E • y) ∈ (A.graph : Set (H × H)) :=
        hSelf.isClosed.isSeqClosed (fun n => A.mem_graph (v n)) hPair
      rcases A.mem_graph_iff.mp hLimit with ⟨yDomain, hyVal, hAy⟩
      have hShiftY : A.realShift E yDomain = x := by
        calc
          A.realShift E yDomain = A yDomain - E • (yDomain : H) := rfl
          _ = (x + E • y) - E • y := by rw [hAy, hyVal]
          _ = x := by abel
      have hUnique :
          yDomain =
            (A.realShiftLinearEquivOfSurjective hSelf E hSurjective).symm x := by
        apply (A.realShift_injective_of_surjective_of_selfAdjoint
          hSelf E hSurjective)
        rw [hShiftY]
        exact (A.realShiftLinearEquivOfSurjective_apply_symm_apply
          hSelf E hSurjective x).symm
      change y =
        A.realShiftAmbientInverseLinearMap hSelf E hSurjective x
      calc
        y = (yDomain : H) := hyVal.symm
        _ = ((A.realShiftLinearEquivOfSurjective
              hSelf E hSurjective).symm x : H) :=
          congrArg Subtype.val hUnique
        _ = A.realShiftAmbientInverseLinearMap hSelf E hSurjective x := rfl)

@[simp] theorem realShiftAmbientInverse_apply
    (A : H →ₗ.[ℝ] H)
    (hSelf : IsSelfAdjoint A)
    (E : ℝ)
    (hSurjective : Function.Surjective (A.realShift E))
    (y : H) :
    A.realShiftAmbientInverse hSelf E hSurjective y =
      ((A.realShiftLinearEquivOfSurjective hSelf E hSurjective).symm y : H) :=
  rfl

end

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The bounded Borel function `(t-E) 1_{B(E,ε)}(t)`. -/
def explicitSpectralBallShiftIndicator
    (E ε : ℝ) (hε : 0 ≤ ε) : ExplicitBoundedBorelRealFunction := by
  classical
  exact
    { toFun := fun t => if t ∈ Metric.ball E ε then t - E else 0
      measurable_toFun :=
        Measurable.ite Metric.isOpen_ball.measurableSet
          (measurable_id.sub measurable_const) measurable_const
      bounded_toFun := by
        refine ⟨ε, ?_⟩
        intro t
        by_cases ht : t ∈ Metric.ball E ε
        · have hdist := (Metric.mem_ball.mp ht).le
          simpa [ht, Real.norm_eq_abs, Real.dist_eq] using hdist
        · simpa [ht] using hε }

/-- The localized shifted coordinate is the shifted coordinate times the ball
indicator. -/
theorem explicitSpectralBallShiftIndicator_eq_shift_mul_indicator
    {E ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    (explicitSpectralBallShiftIndicator E ε hε).toFun t =
      (t - E) *
        (explicitBoundedBorelIndicator (Metric.ball E ε)
          Metric.isOpen_ball.measurableSet).toFun t := by
  classical
  by_cases ht : t ∈ Metric.ball E ε <;>
    simp [explicitSpectralBallShiftIndicator,
      explicitBoundedBorelIndicator, ht]

/-- The localized shifted coordinate has the sharp ball-radius bound. -/
theorem norm_explicitSpectralBallShiftIndicator_le
    {E ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖(explicitSpectralBallShiftIndicator E ε hε).toFun t‖ ≤ ε := by
  by_cases ht : t ∈ Metric.ball E ε
  · have hdistLt : dist t E < ε := Metric.mem_ball.mp ht
    have hdist : |t - E| ≤ ε := by
      simpa [Real.dist_eq] using hdistLt.le
    simpa [explicitSpectralBallShiftIndicator, hdistLt,
      Real.norm_eq_abs] using hdist
  · have hdist : ¬dist t E < ε := by
      simpa only [Metric.mem_ball] using ht
    simpa [explicitSpectralBallShiftIndicator, hdist] using hε

/-- Bounded Borel spectral integration together with the standard contraction
estimate and reduction of the shifted Hamiltonian by spectral projections. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction
    (M : ExplicitWightmanOSReconstructedModel)
    extends ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral M where
  spectralIntegral_norm_le :
    ∀ (f : ExplicitBoundedBorelRealFunction) (C : ℝ), 0 ≤ C →
      (∀ t : ℝ, ‖f.toFun t‖ ≤ C) →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ‖spectralIntegral f ψ‖ ≤ C * ‖ψ‖
  indicator_reduces_realShift :
    ∀ (E : ℝ) (s : Set ℝ) (hs : MeasurableSet s)
      (x : M.canonicalVacuumOrthogonalHamiltonian.domain),
      ∃ xs : M.canonicalVacuumOrthogonalHamiltonian.domain,
        (xs : M.VacuumOrthogonalHilbert) =
          spectralIntegral (explicitBoundedBorelIndicator s hs)
            (x : M.VacuumOrthogonalHilbert) ∧
        M.canonicalVacuumOrthogonalHamiltonian.realShift E xs =
          spectralIntegral (explicitBoundedBorelIndicator s hs)
            (M.canonicalVacuumOrthogonalHamiltonian.realShift E x)

/-- Spectral projection idempotence lifts to the indicator spectral integral on
`Ω⊥`. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction.indicatorIntegral_idempotent
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction M)
    (s : Set ℝ) (hs : MeasurableSet s)
    (ψ : M.VacuumOrthogonalHilbert) :
    F.spectralIntegral (explicitBoundedBorelIndicator s hs)
        (F.spectralIntegral (explicitBoundedBorelIndicator s hs) ψ) =
      F.spectralIntegral (explicitBoundedBorelIndicator s hs) ψ := by
  apply Subtype.ext
  change
    ((F.spectralIntegral (explicitBoundedBorelIndicator s hs)
        (F.spectralIntegral (explicitBoundedBorelIndicator s hs) ψ) :
          M.VacuumOrthogonalHilbert) : M.H) =
      ((F.spectralIntegral (explicitBoundedBorelIndicator s hs) ψ :
          M.VacuumOrthogonalHilbert) : M.H)
  rw [F.spectralIntegral_indicator, F.spectralIntegral_indicator]
  exact M.spectralPVM.idempotent s (ψ : M.H)

/-- A vector localized by the spectral ball has shifted-Hamiltonian norm at most
`ε` times its norm. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction.realShift_norm_le_of_ballSupported
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction M)
    (E ε : ℝ) (hε : 0 < ε)
    (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hx :
      (x : M.VacuumOrthogonalHilbert) =
        F.spectralIntegral
          (explicitBoundedBorelIndicator (Metric.ball E ε)
            Metric.isOpen_ball.measurableSet)
          (x : M.VacuumOrthogonalHilbert)) :
    ‖M.canonicalVacuumOrthogonalHamiltonian.realShift E x‖ ≤
      ε * ‖(x : M.VacuumOrthogonalHilbert)‖ := by
  let f := explicitBoundedBorelIndicator (Metric.ball E ε)
    Metric.isOpen_ball.measurableSet
  let g := explicitSpectralBallShiftIndicator E ε hε.le
  have hMul : ∀ t : ℝ, g.toFun t = (t - E) * f.toFun t := by
    intro t
    exact explicitSpectralBallShiftIndicator_eq_shift_mul_indicator hε.le t
  obtain ⟨z, hzIntegral, hzShift⟩ :=
    F.shiftedCoordinate_graph E f g hMul
      (x : M.VacuumOrthogonalHilbert)
  have hzx : z = x := by
    apply Subtype.ext
    change (z : M.VacuumOrthogonalHilbert) =
      (x : M.VacuumOrthogonalHilbert)
    exact hzIntegral.trans hx.symm
  have hShift :
      M.canonicalVacuumOrthogonalHamiltonian.realShift E x =
        F.spectralIntegral g (x : M.VacuumOrthogonalHilbert) := by
    simpa [hzx] using hzShift
  rw [hShift]
  exact F.spectralIntegral_norm_le g ε hε.le
    (norm_explicitSpectralBallShiftIndicator_le hε.le)
    (x : M.VacuumOrthogonalHilbert)

/-- Surjectivity of the self-adjoint shift yields a single positive spectral ball
whose projection vanishes on every vector.  The radius is obtained from the
closed-graph bounded inverse. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction.surjective_has_uniform_zero_ball
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (E : ℝ)
    (hSurjective : Function.Surjective
      (M.canonicalVacuumOrthogonalHamiltonian.realShift E)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ ψ : M.VacuumOrthogonalHilbert,
        M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0 := by
  let R := M.canonicalVacuumOrthogonalHamiltonian.realShiftAmbientInverse
    hSelf E hSurjective
  let C : ℝ := max ‖R‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right ‖R‖ 1)
  let ε : ℝ := (2 * C)⁻¹
  have hε : 0 < ε := inv_pos.mpr (mul_pos (by norm_num) hC)
  refine ⟨ε, hε, ?_⟩
  intro ψ
  let i := explicitBoundedBorelIndicator (Metric.ball E ε)
    Metric.isOpen_ball.measurableSet
  let y : M.VacuumOrthogonalHilbert := F.spectralIntegral i ψ
  have hyAmbient : (y : M.H) =
      M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) := by
    dsimp [y, i]
    exact F.spectralIntegral_indicator _ _ _
  let e := M.canonicalVacuumOrthogonalHamiltonian.realShiftLinearEquivOfSurjective
    hSelf E hSurjective
  let x : M.canonicalVacuumOrthogonalHamiltonian.domain := e.symm y
  have hShiftX :
      M.canonicalVacuumOrthogonalHamiltonian.realShift E x = y := by
    dsimp [x, e]
    exact M.canonicalVacuumOrthogonalHamiltonian.realShiftLinearEquivOfSurjective_apply_symm_apply
      hSelf E hSurjective y
  obtain ⟨xp, hxpIntegral, hxpShift⟩ :=
    F.indicator_reduces_realShift E (Metric.ball E ε)
      Metric.isOpen_ball.measurableSet x
  have hIy : F.spectralIntegral i y = y := by
    simpa [y, i] using F.indicatorIntegral_idempotent
      (Metric.ball E ε) Metric.isOpen_ball.measurableSet ψ
  have hShiftXp :
      M.canonicalVacuumOrthogonalHamiltonian.realShift E xp = y := by
    calc
      M.canonicalVacuumOrthogonalHamiltonian.realShift E xp =
          F.spectralIntegral i
            (M.canonicalVacuumOrthogonalHamiltonian.realShift E x) := by
              simpa [i] using hxpShift
      _ = F.spectralIntegral i y := by rw [hShiftX]
      _ = y := hIy
  have hInjective : Function.Injective
      (M.canonicalVacuumOrthogonalHamiltonian.realShift E) :=
    M.canonicalVacuumOrthogonalHamiltonian.realShift_injective_of_surjective_of_selfAdjoint
      hSelf E hSurjective
  have hxpEq : xp = x := hInjective (hShiftXp.trans hShiftX.symm)
  have hxSupported :
      (x : M.VacuumOrthogonalHilbert) = F.spectralIntegral i
        (x : M.VacuumOrthogonalHilbert) := by
    calc
      (x : M.VacuumOrthogonalHilbert) =
          (xp : M.VacuumOrthogonalHilbert) :=
        congrArg Subtype.val hxpEq.symm
      _ = F.spectralIntegral i
          (x : M.VacuumOrthogonalHilbert) := by
            simpa [i] using hxpIntegral
  have hLocal := F.realShift_norm_le_of_ballSupported E ε hε x (by
    simpa [i] using hxSupported)
  have hInverseBound :
      ‖(x : M.VacuumOrthogonalHilbert)‖ ≤ C * ‖y‖ := by
    calc
      ‖(x : M.VacuumOrthogonalHilbert)‖ = ‖R y‖ := by
        rfl
      _ ≤ ‖R‖ * ‖y‖ := ContinuousLinearMap.le_opNorm R y
      _ ≤ C * ‖y‖ :=
        mul_le_mul_of_nonneg_right (le_max_left ‖R‖ 1) (norm_nonneg y)
  have hyNorm : ‖y‖ ≤ (ε * C) * ‖y‖ := by
    calc
      ‖y‖ =
          ‖M.canonicalVacuumOrthogonalHamiltonian.realShift E x‖ := by
            rw [hShiftX]
      _ ≤ ε * ‖(x : M.VacuumOrthogonalHilbert)‖ := hLocal
      _ ≤ ε * (C * ‖y‖) :=
        mul_le_mul_of_nonneg_left hInverseBound hε.le
      _ = (ε * C) * ‖y‖ := by ring
  have hεC : ε * C = (1 / 2 : ℝ) := by
    dsimp [ε]
    field_simp [ne_of_gt hC]
  rw [hεC] at hyNorm
  have hyZero : y = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg y]
  rw [← hyAmbient, hyZero]
  rfl

/-- The reduction package closes both directions of the ball functional calculus. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction.toBallFunctionalCalculus
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian) :
    ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M :=
  { ballVanish_has_preimage := F.ballVanish_has_preimage
    surjective_has_uniform_zero_ball :=
      F.surjective_has_uniform_zero_ball hSelf }

/-- End-to-end exact-gap endpoint with no independent uniform resolvent-ball input. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_boundedBorelSpectralReduction
    (M : ExplicitWightmanOSReconstructedModel)
    (F : ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralReduction M)
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
      (((F.toBallFunctionalCalculus hSelf).toCanonicalRestrictedPVMSpectralTheorem
          hSelf hSupport).toCanonicalPVMOpenSupportBridge
            hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact
    explicit_wightman_os_exact_gap_pvm_open_support_of_ball_functionalCalculus
      M (F.toBallFunctionalCalculus hSelf)
        hSelf D hGap hExactSpectrum hSupport

end

end MathlibAnalytic
end MGAP4D
