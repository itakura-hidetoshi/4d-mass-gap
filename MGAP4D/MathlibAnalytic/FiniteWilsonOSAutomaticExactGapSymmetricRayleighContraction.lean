import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapHilbertMatrixContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A real symmetric continuous linear operator is controlled by its absolute
quadratic form.  This is the real polarization step needed to replace the
all-matrix-coefficient cluster input by a Rayleigh-type input. -/
theorem real_symmetric_matrix_coefficient_le_of_abs_quadratic_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (C : ℝ)
    (hsymm : ∀ x y : E, inner ℝ (T x) y = inner ℝ (T y) x)
    (hquad : ∀ z : E, |inner ℝ (T z) z| ≤ C * ‖z‖ ^ 2)
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    inner ℝ (T x) y ≤ C := by
  have hpolar :
      4 * inner ℝ (T x) y =
        inner ℝ (T (x + y)) (x + y) -
          inner ℝ (T (x - y)) (x - y) := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right]
    rw [hsymm y x]
    ring
  have hdiff :
      inner ℝ (T (x + y)) (x + y) -
          inner ℝ (T (x - y)) (x - y) ≤
        |inner ℝ (T (x + y)) (x + y)| +
          |inner ℝ (T (x - y)) (x - y)| := by
    calc
      inner ℝ (T (x + y)) (x + y) -
          inner ℝ (T (x - y)) (x - y) ≤
        |inner ℝ (T (x + y)) (x + y)| -
          inner ℝ (T (x - y)) (x - y) :=
            sub_le_sub_right (le_abs_self _) _
      _ ≤ |inner ℝ (T (x + y)) (x + y)| +
          |inner ℝ (T (x - y)) (x - y)| := by
            rw [sub_eq_add_neg]
            gcongr
            exact neg_le_abs _
  have hquadSum :
      |inner ℝ (T (x + y)) (x + y)| +
          |inner ℝ (T (x - y)) (x - y)| ≤
        C * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by
    calc
      |inner ℝ (T (x + y)) (x + y)| +
          |inner ℝ (T (x - y)) (x - y)| ≤
        C * ‖x + y‖ ^ 2 + C * ‖x - y‖ ^ 2 :=
          add_le_add (hquad (x + y)) (hquad (x - y))
      _ = C * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by ring
  have hparallelogram : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 4 := by
    calc
      ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 =
          2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
        parallelogram_law_with_norm ℝ x y
      _ = 4 := by rw [hx, hy]; norm_num
  have hfour : 4 * inner ℝ (T x) y ≤ 4 * C := by
    calc
      4 * inner ℝ (T x) y =
          inner ℝ (T (x + y)) (x + y) -
            inner ℝ (T (x - y)) (x - y) := hpolar
      _ ≤ |inner ℝ (T (x + y)) (x + y)| +
          |inner ℝ (T (x - y)) (x - y)| := hdiff
      _ ≤ C * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := hquadSum
      _ = 4 * C := by rw [hparallelogram]; ring
  linarith

/-- Finite Wilson transfer-state data in which exact-gap contraction is given
by symmetry plus an absolute Rayleigh quadratic-form estimate. -/
structure FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  StateSpace : Type
  [stateNormedAddCommGroup : NormedAddCommGroup StateSpace]
  [stateInnerProductSpace : InnerProductSpace ℝ StateSpace]
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  decayAmplitude_nonneg : ∀ O : Observable, 0 ≤ decayAmplitude O
  transferOperator : ℕ → StateSpace →L[ℝ] StateSpace
  transferSymmetric :
    ∀ (n : ℕ) (x y : StateSpace),
      inner ℝ (transferOperator n x) y =
        inner ℝ (transferOperator n y) x
  rayleighAbsBound :
    ∀ (n : ℕ) (x : StateSpace),
      |inner ℝ (transferOperator n x) x| ≤
        exactGapClusterContractionRatio * ‖x‖ ^ 2
  correlationState : ℕ → Observable → ℕ → StateSpace
  correlationReadout : ℕ → Observable → StateSpace →L[ℝ] ℝ
  state_succ :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      correlationState n O (Nat.succ r) =
        transferOperator n (correlationState n O r)
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O (correlationState n O r)
  readoutInitialStateBound :
    ∀ (n : ℕ) (O : Observable),
      ‖correlationReadout n O‖ * ‖correlationState n O 0‖ ≤
        decayAmplitude O
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))

attribute [instance]
  FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData.stateInnerProductSpace

/-- Polarization converts the symmetric Rayleigh package into the Hilbert
matrix-coefficient package. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData.toHilbertMatrixData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W) :
    FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData W :=
  { Observable := D.Observable
    StateSpace := D.StateSpace
    stateNormedAddCommGroup := D.stateNormedAddCommGroup
    stateInnerProductSpace := D.stateInnerProductSpace
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    decayAmplitude_nonneg := D.decayAmplitude_nonneg
    transferOperator := D.transferOperator
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    matrixCoefficientBound := by
      intro n x y hx hy
      simpa using
        real_symmetric_matrix_coefficient_le_of_abs_quadratic_bound
          (D.transferOperator n) exactGapClusterContractionRatio
          (D.transferSymmetric n) (D.rayleighAbsBound n) hx hy
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Symmetric Rayleigh control generates the exact-gap operator contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_symmetric_rayleigh
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_matrix_coefficients
    D.toHilbertMatrixData n

/-- Symmetric Rayleigh control generates the full finite-volume exact-gap
connected-correlation estimate. -/
theorem finite_wilson_exact_gap_bound_of_symmetric_rayleigh
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_hilbert_matrix_contraction
    D.toHilbertMatrixData n O r

/-- Symmetric Rayleigh control implies continuum clustering after pointwise
convergence. -/
theorem finite_wilson_exact_gap_symmetric_rayleigh_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W) :
    D.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_hilbert_matrix_contraction_passes_to_limit
    D.toHilbertMatrixData

/-- The continuum connected correlation inherits the exact-gap estimate
constructed from symmetry and the Rayleigh bound. -/
theorem finite_wilson_exact_gap_symmetric_rayleigh_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_hilbert_matrix_contraction_continuum_bound
    D.toHilbertMatrixData O r

end

end MathlibAnalytic
end MGAP4D
