import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMFunctionalCalculusCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Construct the ball-local inverse of the canonical restricted Hamiltonian from an
operator-valued bounded Borel spectral integral.  The preceding local and ball
functional-calculus package is retained in
`WightmanOSCanonicalRestrictedHamiltonianPVMFunctionalCalculusCore`.
-/

/-- A real Borel function equipped with an explicit uniform bound. -/
structure ExplicitBoundedBorelRealFunction where
  toFun : ℝ → ℝ
  measurable_toFun : Measurable toFun
  bounded_toFun : ∃ C : ℝ, ∀ t : ℝ, ‖toFun t‖ ≤ C

/-- The constant-one bounded Borel function. -/
def explicitBoundedBorelOne : ExplicitBoundedBorelRealFunction where
  toFun := fun _ => 1
  measurable_toFun := measurable_const
  bounded_toFun := ⟨1, by intro t; simp⟩

/-- Indicator of a measurable real set as a bounded Borel function. -/
def explicitBoundedBorelIndicator
    (s : Set ℝ) (hs : MeasurableSet s) :
    ExplicitBoundedBorelRealFunction := by
  classical
  exact
    { toFun := fun t => if t ∈ s then 1 else 0
      measurable_toFun :=
        Measurable.ite hs measurable_const measurable_const
      bounded_toFun := by
        refine ⟨1, ?_⟩
        intro t
        by_cases ht : t ∈ s <;> simp [ht] }

/-- Difference of two bounded Borel functions. -/
def explicitBoundedBorelSub
    (f g : ExplicitBoundedBorelRealFunction) :
    ExplicitBoundedBorelRealFunction where
  toFun := fun t => f.toFun t - g.toFun t
  measurable_toFun := f.measurable_toFun.sub g.measurable_toFun
  bounded_toFun := by
    obtain ⟨Cf, hf⟩ := f.bounded_toFun
    obtain ⟨Cg, hg⟩ := g.bounded_toFun
    refine ⟨Cf + Cg, ?_⟩
    intro t
    calc
      ‖f.toFun t - g.toFun t‖ ≤ ‖f.toFun t‖ + ‖g.toFun t‖ :=
        norm_sub_le _ _
      _ ≤ Cf + Cg := add_le_add (hf t) (hg t)

/-- The explicit ball-truncated reciprocal as a typed bounded Borel function. -/
def explicitSpectralBallTruncatedReciprocal
    (E ε : ℝ) (hε : 0 < ε) : ExplicitBoundedBorelRealFunction where
  toFun := spectralBallTruncatedReciprocal E ε
  measurable_toFun := measurable_spectralBallTruncatedReciprocal E ε
  bounded_toFun :=
    ⟨ε⁻¹, norm_spectralBallTruncatedReciprocal_le hε⟩

/-- Pointwise shifted-coordinate cancellation, expressed as one minus the ball
indicator. -/
theorem explicitBoundedBorel_one_sub_ballIndicator_eq_shift_mul_truncatedReciprocal
    {E ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (explicitBoundedBorelSub explicitBoundedBorelOne
      (explicitBoundedBorelIndicator (Metric.ball E ε)
        Metric.isOpen_ball.measurableSet)).toFun t =
      (t - E) *
        (explicitSpectralBallTruncatedReciprocal E ε hε).toFun t := by
  classical
  by_cases ht : t ∈ Metric.ball E ε
  · simp [explicitBoundedBorelSub, explicitBoundedBorelOne,
      explicitBoundedBorelIndicator,
      explicitSpectralBallTruncatedReciprocal, ht,
      spectralBallTruncatedReciprocal_of_mem ht]
  · have hCancel :=
      sub_mul_spectralBallTruncatedReciprocal
        (E := E) (ε := ε) (t := t) hε ht
    simpa [explicitBoundedBorelSub, explicitBoundedBorelOne,
      explicitBoundedBorelIndicator,
      explicitSpectralBallTruncatedReciprocal, ht] using hCancel.symm

/-- Actual bounded Borel spectral integral for the canonical restricted
Hamiltonian.

Indicator functions recover the ambient PVM after inclusion into the physical
Hilbert space.  The shifted-coordinate graph law states that whenever
`g(t) = (t-E)f(t)`, the vector `∫ f dP ψ` lies in the restricted Hamiltonian
domain and its real shift is `∫ g dP ψ`. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral
    (M : ExplicitWightmanOSReconstructedModel) where
  spectralIntegral :
    ExplicitBoundedBorelRealFunction →
      M.VacuumOrthogonalHilbert →L[ℝ] M.VacuumOrthogonalHilbert
  spectralIntegral_one :
    ∀ ψ : M.VacuumOrthogonalHilbert,
      spectralIntegral explicitBoundedBorelOne ψ = ψ
  spectralIntegral_sub :
    ∀ (f g : ExplicitBoundedBorelRealFunction)
      (ψ : M.VacuumOrthogonalHilbert),
      spectralIntegral (explicitBoundedBorelSub f g) ψ =
        spectralIntegral f ψ - spectralIntegral g ψ
  spectralIntegral_indicator :
    ∀ (s : Set ℝ) (hs : MeasurableSet s)
      (ψ : M.VacuumOrthogonalHilbert),
      ((spectralIntegral (explicitBoundedBorelIndicator s hs) ψ :
          M.VacuumOrthogonalHilbert) : M.H) =
        M.spectralPVM.projection s (ψ : M.H)
  shiftedCoordinate_graph :
    ∀ (E : ℝ) (f g : ExplicitBoundedBorelRealFunction),
      (∀ t : ℝ, g.toFun t = (t - E) * f.toFun t) →
      ∀ ψ : M.VacuumOrthogonalHilbert,
        ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
          (x : M.VacuumOrthogonalHilbert) = spectralIntegral f ψ ∧
            M.canonicalVacuumOrthogonalHamiltonian.realShift E x =
              spectralIntegral g ψ

/-- The bounded Borel spectral integral constructs the missing ball-local
preimage by integrating the explicit truncated reciprocal. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral.ballVanish_has_preimage
    {M : ExplicitWightmanOSReconstructedModel}
    (F :
      ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral M)
    (E ε : ℝ) (hε : 0 < ε)
    (ψ : M.VacuumOrthogonalHilbert)
    (hZero :
      M.spectralPVM.projection (Metric.ball E ε) (ψ : M.H) = 0) :
    ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
      M.canonicalVacuumOrthogonalHamiltonian.realShift E x = ψ := by
  let f := explicitSpectralBallTruncatedReciprocal E ε hε
  let i := explicitBoundedBorelIndicator (Metric.ball E ε)
    Metric.isOpen_ball.measurableSet
  let g := explicitBoundedBorelSub explicitBoundedBorelOne i
  have hMul : ∀ t : ℝ, g.toFun t = (t - E) * f.toFun t := by
    intro t
    exact
      explicitBoundedBorel_one_sub_ballIndicator_eq_shift_mul_truncatedReciprocal
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
          F.spectralIntegral explicitBoundedBorelOne ψ -
            F.spectralIntegral i ψ := by
              dsimp [g]
              exact F.spectralIntegral_sub explicitBoundedBorelOne i ψ
      _ = ψ - 0 := by
        rw [F.spectralIntegral_one, hIndicatorZero]
      _ = ψ := sub_zero ψ
  exact hShift.trans hIntegralG

/-- Combining the constructed inverse with the independent uniform resolvent-ball
law yields the complete ball functional-calculus package used downstream. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral.toBallFunctionalCalculus
    {M : ExplicitWightmanOSReconstructedModel}
    (F :
      ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral M)
    (hUniform :
      ∀ E : ℝ,
        Function.Surjective
            (M.canonicalVacuumOrthogonalHamiltonian.realShift E) →
          ∃ ε : ℝ, 0 < ε ∧
            ∀ ψ : M.VacuumOrthogonalHilbert,
              M.spectralPVM.projection
                  (Metric.ball E ε) (ψ : M.H) = 0) :
    ExplicitWightmanOSCanonicalRestrictedPVMBallFunctionalCalculus M :=
  { ballVanish_has_preimage :=
      F.ballVanish_has_preimage
    surjective_has_uniform_zero_ball := hUniform }

/-- End-to-end exact-gap endpoint from the actual bounded Borel spectral integral
and the still-independent uniform resolvent-ball direction. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_boundedBorelSpectralIntegral
    (M : ExplicitWightmanOSReconstructedModel)
    (F :
      ExplicitWightmanOSCanonicalRestrictedPVMBoundedBorelSpectralIntegral M)
    (hUniform :
      ∀ E : ℝ,
        Function.Surjective
            (M.canonicalVacuumOrthogonalHamiltonian.realShift E) →
          ∃ ε : ℝ, 0 < ε ∧
            ∀ ψ : M.VacuumOrthogonalHilbert,
              M.spectralPVM.projection
                  (Metric.ball E ε) (ψ : M.H) = 0)
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
      (((F.toBallFunctionalCalculus hUniform).toCanonicalRestrictedPVMSpectralTheorem
          hSelf hSupport).toCanonicalPVMOpenSupportBridge
            hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact
    explicit_wightman_os_exact_gap_pvm_open_support_of_ball_functionalCalculus
      M (F.toBallFunctionalCalculus hUniform)
        hSelf D hGap hExactSpectrum hSupport

end

end MathlibAnalytic
end MGAP4D
