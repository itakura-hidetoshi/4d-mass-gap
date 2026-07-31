import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetFiniteDimensionalCompressionTraceDeterminantLimit
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- One center/radius/target point in a Taylor parameter box. -/
structure ContinuousLinearMapTaylorParameterPoint where
  center : ℝ
  radius : ℝ
  target : ℝ

/-- A closed Taylor parameter box lying strictly inside a spectral gap. -/
structure ContinuousLinearMapClosedTaylorParameterBox (gap : ℝ) where
  deltaMin : ℝ
  lambdaMin : ℝ
  lambdaMax : ℝ
  rMax : ℝ
  delta_le_gap : deltaMin ≤ gap
  lambda_bounds : lambdaMin ≤ lambdaMax
  lambdaMax_lt_delta : lambdaMax < deltaMin
  rMax_nonneg : 0 ≤ rMax
  rMax_lt_margin : rMax < deltaMin - lambdaMax

namespace ContinuousLinearMapClosedTaylorParameterBox

/-- Membership in the full closed Taylor parameter box. -/
def Contains {gap : ℝ}
    (P : ContinuousLinearMapClosedTaylorParameterBox gap)
    (p : ContinuousLinearMapTaylorParameterPoint) : Prop :=
  P.lambdaMin ≤ p.center ∧ p.center ≤ P.lambdaMax ∧
    0 ≤ p.radius ∧ p.radius ≤ P.rMax ∧
      ‖p.target - p.center‖ ≤ p.radius

/-- Every target point in the box lies below the common upper spectral edge. -/
theorem target_le_upper {gap : ℝ}
    (P : ContinuousLinearMapClosedTaylorParameterBox gap)
    {p : ContinuousLinearMapTaylorParameterPoint}
    (hp : P.Contains p) :
    p.target ≤ P.lambdaMax + P.rMax := by
  have hdiff : p.target - p.center ≤ p.radius := by
    calc
      p.target - p.center ≤ |p.target - p.center| := le_abs_self _
      _ = ‖p.target - p.center‖ := by rw [Real.norm_eq_abs]
      _ ≤ p.radius := hp.2.2.2.2
  linarith [hp.2.1, hp.2.2.2.1]

/-- The common upper spectral edge of the box remains strictly below the gap. -/
theorem upper_lt_gap {gap : ℝ}
    (P : ContinuousLinearMapClosedTaylorParameterBox gap) :
    P.lambdaMax + P.rMax < gap := by
  linarith [P.rMax_lt_margin, P.lambdaMax_lt_delta, P.delta_le_gap]

/-- Every target point in the box is strictly subgap. -/
theorem target_lt_gap {gap : ℝ}
    (P : ContinuousLinearMapClosedTaylorParameterBox gap)
    {p : ContinuousLinearMapTaylorParameterPoint}
    (hp : P.Contains p) :
    p.target < gap :=
  lt_of_le_of_lt (P.target_le_upper hp) P.upper_lt_gap

end ContinuousLinearMapClosedTaylorParameterBox

/-- A finite real polynomial evaluated on a continuous endomorphism.  The
powers retain their noncommutative operator multiplication; no commutativity
between two different operators is used anywhere in the package. -/
def continuousLinearMapPolynomial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (coeff : ℕ → ℝ) (degree : ℕ) (A : V →L[ℝ] V) : V →L[ℝ] V :=
  ∑ n ∈ Finset.range (degree + 1), coeff n • A ^ n

/-- Polynomial evaluation is continuous in operator norm. -/
theorem continuous_continuousLinearMapPolynomial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (coeff : ℕ → ℝ) (degree : ℕ) :
    Continuous (continuousLinearMapPolynomial (V := V) coeff degree) := by
  unfold continuousLinearMapPolynomial
  fun_prop

/-- Trace of a finite operator polynomial. -/
def continuousLinearMapPolynomialTrace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (coeff : ℕ → ℝ) (degree : ℕ) (A : V →L[ℝ] V) : ℝ :=
  continuousLinearMapTrace (continuousLinearMapPolynomial coeff degree A)

/-- Determinant of a finite operator polynomial. -/
def continuousLinearMapPolynomialDet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (coeff : ℕ → ℝ) (degree : ℕ) (A : V →L[ℝ] V) : ℝ :=
  (continuousLinearMapPolynomial coeff degree A).det

/-- Polynomial trace is continuous in operator norm. -/
theorem continuous_continuousLinearMapPolynomialTrace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (coeff : ℕ → ℝ) (degree : ℕ) :
    Continuous (continuousLinearMapPolynomialTrace (V := V) coeff degree) := by
  unfold continuousLinearMapPolynomialTrace
  fun_prop

/-- Polynomial determinant is continuous in operator norm. -/
theorem continuous_continuousLinearMapPolynomialDet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (coeff : ℕ → ℝ) (degree : ℕ) :
    Continuous (continuousLinearMapPolynomialDet (V := V) coeff degree) := by
  unfold continuousLinearMapPolynomialDet
  exact ContinuousLinearMap.continuous_det.comp
    (continuous_continuousLinearMapPolynomial coeff degree)

/-- The `n`th finite-dimensional spectral moment `tr(A^n)`. -/
def continuousLinearMapSpectralMoment
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) : ℝ :=
  continuousLinearMapTrace (A ^ n)

/-- The finite vector of moments from degree zero through `order`. -/
def continuousLinearMapSpectralMomentJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (order : ℕ) (A : V →L[ℝ] V) : Fin (order + 1) → ℝ :=
  fun n => continuousLinearMapSpectralMoment n.1 A

/-- Every individual spectral moment is continuous. -/
theorem continuous_continuousLinearMapSpectralMoment
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) :
    Continuous (continuousLinearMapSpectralMoment (V := V) n) := by
  unfold continuousLinearMapSpectralMoment
  fun_prop

/-- Every finite moment jet is continuous for the supremum norm on the finite
coordinate space. -/
theorem continuous_continuousLinearMapSpectralMomentJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (order : ℕ) :
    Continuous (continuousLinearMapSpectralMomentJet (V := V) order) := by
  unfold continuousLinearMapSpectralMomentJet
  apply continuous_pi
  intro n
  exact continuous_continuousLinearMapSpectralMoment n.1

/-- Norm of a compression is controlled by the three operator norms. -/
theorem continuousLinearMapCompression_norm_le
    {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (A : E →L[ℝ] E) :
    ‖continuousLinearMapCompression J Q A‖ ≤ ‖Q‖ * ‖A‖ * ‖J‖ := by
  calc
    ‖continuousLinearMapCompression J Q A‖ = ‖Q.comp (A.comp J)‖ := rfl
    _ ≤ ‖Q‖ * ‖A.comp J‖ := Q.opNorm_comp_le (A.comp J)
    _ ≤ ‖Q‖ * (‖A‖ * ‖J‖) :=
      mul_le_mul_of_nonneg_left (A.opNorm_comp_le J) (norm_nonneg Q)
    _ = ‖Q‖ * ‖A‖ * ‖J‖ := by ring

/-- A common operator-norm bound propagates to every positive power. -/
theorem continuousLinearMap_pow_succ_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖A‖ ≤ q) (n : ℕ) :
    ‖A ^ (n + 1)‖ ≤ q ^ (n + 1) := by
  induction n with
  | zero => simpa using hA
  | succ n ih =>
      calc
        ‖A ^ (Nat.succ n + 1)‖ = ‖A ^ (n + 1) * A‖ := by
          rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
        _ ≤ ‖A ^ (n + 1)‖ * ‖A‖ := norm_mul_le _ _
        _ ≤ q ^ (n + 1) * q :=
          mul_le_mul ih hA (norm_nonneg A) (pow_nonneg hq (n + 1))
        _ = q ^ (Nat.succ n + 1) := by
          rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]

/-- Uniform operator-norm convergence on a set passes through every continuous
observable once the limit family has a common bound in a finite-dimensional
domain.  The proof uses compactness of a closed ball and Heine--Cantor; it is
not restricted to polynomial or spectral observables. -/
theorem finiteDimensional_continuousObservable_tendsto_uniformOn
    {α ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter α} {s : Set ι}
    (A : α → ι → X) (A0 : ι → X)
    (Phi : X → Y) (hPhi : Continuous Phi)
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ‖Phi (A a i) - Phi (A0 i)‖ < epsilon := by
  intro epsilon hepsilon
  let C : Set X := Metric.closedBall 0 (R + 1)
  have hCcompact : IsCompact C := isCompact_closedBall 0 (R + 1)
  have hUniform : UniformContinuousOn Phi C :=
    hCcompact.uniformContinuousOn_of_continuous hPhi.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hUniform) epsilon hepsilon with
    ⟨delta, hdelta, hmodulus⟩
  let eta : ℝ := min delta 1
  have heta : 0 < eta := lt_min hdelta zero_lt_one
  have hApprox := hA eta heta
  filter_upwards [hApprox] with a ha
  intro i hi
  have hdiffDelta : ‖A a i - A0 i‖ < delta :=
    lt_of_lt_of_le (ha i hi) (min_le_left delta 1)
  have hdiffOne : ‖A a i - A0 i‖ < 1 :=
    lt_of_lt_of_le (ha i hi) (min_le_right delta 1)
  have hA0C : A0 i ∈ C := by
    have hnorm : ‖A0 i‖ ≤ R + 1 :=
      (hA0 i hi).trans (by linarith)
    simpa [C, Metric.mem_closedBall, dist_zero_right] using hnorm
  have hAnorm : ‖A a i‖ ≤ R + 1 := by
    calc
      ‖A a i‖ = ‖A a i - A0 i + A0 i‖ := by rw [sub_add_cancel]
      _ ≤ ‖A a i - A0 i‖ + ‖A0 i‖ := norm_add_le _ _
      _ ≤ 1 + R := add_le_add (le_of_lt hdiffOne) (hA0 i hi)
      _ = R + 1 := by ring
  have hAC : A a i ∈ C := by
    simpa [C, Metric.mem_closedBall, dist_zero_right] using hAnorm
  have hdist : dist (A a i) (A0 i) < delta := by
    simpa [dist_eq_norm] using hdiffDelta
  have hout := hmodulus (A a i) hAC (A0 i) hA0C hdist
  simpa [dist_eq_norm] using hout

namespace ContinuousLinearMapOpenResolventNormBoundData

variable {E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Uniform compressed-resolvent norm bound on a closed subgap half-line. -/
theorem resolvent_finiteDimensionalCompression_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {u lambda : ℝ} (hu : u < D.gap) (hlambda : lambda ≤ u) :
    ‖continuousLinearMapCompression J Q (D.resolvent lambda)‖ ≤
      ‖Q‖ * (D.gap - u)⁻¹ * ‖J‖ := by
  calc
    ‖continuousLinearMapCompression J Q (D.resolvent lambda)‖ ≤
        ‖Q‖ * ‖D.resolvent lambda‖ * ‖J‖ :=
      continuousLinearMapCompression_norm_le J Q (D.resolvent lambda)
    _ ≤ ‖Q‖ * (D.gap - u)⁻¹ * ‖J‖ := by
      gcongr
      exact D.resolvent_norm_le_on_Iic hu hlambda

/-- Uniform norm bound for every compressed Taylor derivative on a closed
subgap half-line. -/
theorem iteratedDeriv_finiteDimensionalCompression_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) {u lambda : ℝ} (hu : u < D.gap) (hlambda : lambda ≤ u) :
    ‖continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k D.resolvent lambda)‖ ≤
      ‖Q‖ * ((k.factorial : ℝ) * (D.gap - u)⁻¹ ^ (k + 1)) * ‖J‖ := by
  let q : ℝ := (D.gap - u)⁻¹
  have hmargin : 0 < D.gap - u := sub_pos.mpr hu
  have hq0 : 0 ≤ q := inv_nonneg.mpr hmargin.le
  have hlambdaGap : lambda < D.gap := lt_of_le_of_lt hlambda hu
  have hres : ‖D.resolvent lambda‖ ≤ q := by
    simpa [q] using D.resolvent_norm_le_on_Iic hu hlambda
  have hpow : ‖D.resolvent lambda ^ (k + 1)‖ ≤ q ^ (k + 1) :=
    continuousLinearMap_pow_succ_norm_le
      (D.resolvent lambda) hq0 hres k
  have hderiv :
      ‖_root_.iteratedDeriv k D.resolvent lambda‖ ≤
        (k.factorial : ℝ) * q ^ (k + 1) := by
    rw [(D.toContinuousLinearMapOpenResolventData).iteratedDeriv k hlambdaGap]
    calc
      ‖(k.factorial : ℝ) • D.resolvent lambda ^ (k + 1)‖ =
          (k.factorial : ℝ) * ‖D.resolvent lambda ^ (k + 1)‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ (k.factorial : ℝ) * q ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  calc
    ‖continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k D.resolvent lambda)‖ ≤
      ‖Q‖ * ‖_root_.iteratedDeriv k D.resolvent lambda‖ * ‖J‖ :=
        continuousLinearMapCompression_norm_le J Q _
    _ ≤ ‖Q‖ * ((k.factorial : ℝ) * q ^ (k + 1)) * ‖J‖ := by
      gcongr
    _ = ‖Q‖ * ((k.factorial : ℝ) * (D.gap - u)⁻¹ ^ (k + 1)) * ‖J‖ := by
      rfl

end ContinuousLinearMapOpenResolventNormBoundData

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Every continuous observable of a compressed fixed Taylor derivative
converges uniformly on compact strict-subgap spectral sets. -/
theorem iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖Phi (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
  let R : ℝ :=
    ‖Q‖ * ((k.factorial : ℝ) * (gap - u)⁻¹ ^ (k + 1)) * ‖J‖
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hlimit :
      ∀ lambda ∈ K,
        ‖continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)‖ ≤ R := by
    intro lambda hlambda
    have h :=
      L.iteratedDeriv_finiteDimensionalCompression_norm_le_on_Iic
        J Q k (by simpa [hLgap] using hu) (hKu hlambda)
    simpa [R, hLgap, hLresolvent] using h
  have hoperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu
  exact
    finiteDimensional_continuousObservable_tendsto_uniformOn
      (l := l) (s := K)
      (fun a lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) lambda))
      (fun lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))
      Phi hPhi R hR hlimit hoperator

/-- A finite Taylor jet may carry a different continuous observable at each
jet level, with simultaneous compact-uniform convergence. -/
theorem iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : ℕ → (V →L[ℝ] V) → W) (hPhi : ∀ k, Continuous (Phi k))
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
    intro k hk
    exact S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (Phi k) (hPhi k)
      k K hKcompact hKu hu epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K,
        ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2
      fun k hk' => hk k hk'
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

/-- Determinants of compressed Taylor derivatives now converge uniformly on
compact strict-subgap spectral sets. -/
theorem iteratedDeriv_det_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        |(continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)).det -
          (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (fun A : V →L[ℝ] V => A.det)
      ContinuousLinearMap.continuous_det k K hKcompact hKu hu

/-- Whole finite Taylor jets have simultaneous compact-uniform determinant
convergence. -/
theorem iteratedDeriv_det_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        |(continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)).det -
          (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
      B L hLgap hLresolvent J Q
      (fun _ A : V →L[ℝ] V => A.det)
      (fun _ => ContinuousLinearMap.continuous_det)
      order K hKcompact hKu hu

/-- Finite operator polynomials of compressed Taylor derivatives converge in
operator norm uniformly on compact strict-subgap sets. -/
theorem iteratedDeriv_polynomial_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (coeff : ℕ → ℝ) (degree k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖continuousLinearMapPolynomial coeff degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapPolynomial coeff degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon :=
  S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
    B L hLgap hLresolvent J Q
    (continuousLinearMapPolynomial coeff degree)
    (continuous_continuousLinearMapPolynomial coeff degree)
    k K hKcompact hKu hu

/-- Traces of finite operator polynomials converge compact-uniformly. -/
theorem iteratedDeriv_polynomialTrace_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (coeff : ℕ → ℝ) (degree k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        |continuousLinearMapPolynomialTrace coeff degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapPolynomialTrace coeff degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q
      (continuousLinearMapPolynomialTrace coeff degree)
      (continuous_continuousLinearMapPolynomialTrace coeff degree)
      k K hKcompact hKu hu

/-- Determinants of finite operator polynomials converge compact-uniformly. -/
theorem iteratedDeriv_polynomialDet_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (coeff : ℕ → ℝ) (degree k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        |continuousLinearMapPolynomialDet coeff degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapPolynomialDet coeff degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q
      (continuousLinearMapPolynomialDet coeff degree)
      (continuous_continuousLinearMapPolynomialDet coeff degree)
      k K hKcompact hKu hu

/-- Every finite vector of spectral moments converges compact-uniformly. -/
theorem iteratedDeriv_spectralMomentJet_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (momentOrder k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖continuousLinearMapSpectralMomentJet momentOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapSpectralMomentJet momentOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon :=
  S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
    B L hLgap hLresolvent J Q
    (continuousLinearMapSpectralMomentJet momentOrder)
    (continuous_continuousLinearMapSpectralMomentJet momentOrder)
    k K hKcompact hKu hu

/-- Every finite Taylor jet and every finite spectral-moment jet converge
simultaneously. -/
theorem iteratedDeriv_spectralMomentJet_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (momentOrder taylorOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ taylorOrder, ∀ lambda ∈ K,
        ‖continuousLinearMapSpectralMomentJet momentOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapSpectralMomentJet momentOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon :=
  S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    B L hLgap hLresolvent J Q
    (fun _ => continuousLinearMapSpectralMomentJet momentOrder)
    (fun _ => continuous_continuousLinearMapSpectralMomentJet momentOrder)
    taylorOrder K hKcompact hKu hu

/-- Every continuous observable of compressed Taylor partial sums converges
uniformly on a full closed Taylor box for arbitrary joint time/degree nets. -/
theorem taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        ‖Phi (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          Phi (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon := by
  let upper : ℝ := box.lambdaMax + box.rMax
  let R : ℝ := ‖Q‖ * (gap - upper)⁻¹ * ‖J‖
  have hupper : upper < gap := by
    simpa [upper] using box.upper_lt_gap
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hlimit : ∀ p ∈ {p | box.Contains p},
      ‖continuousLinearMapCompression J Q
          (S.limitResolvent p.target)‖ ≤ R := by
    intro p hp
    have h := L.resolvent_finiteDimensionalCompression_norm_le_on_Iic
      J Q (by simpa [hLgap] using hupper) (box.target_le_upper hp)
    simpa [R, upper, hLgap, hLresolvent] using h
  have hoperator : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ p ∈ {p | box.Contains p},
        ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b)) -
          continuousLinearMapCompression J Q
              (S.limitResolvent p.target)‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree
        box.delta_le_gap box.lambda_bounds box.lambdaMax_lt_delta
        box.rMax_nonneg box.rMax_lt_margin eta heta
    filter_upwards [h] with b hb
    intro p hp
    exact hb p.center p.radius p.target
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    (l := m) (s := {p | box.Contains p})
    (fun b p => continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum
        (F (a b)) p.center p.target (degree b)))
    (fun p => continuousLinearMapCompression J Q
      (S.limitResolvent p.target))
    Phi hPhi R hR hlimit hoperator

/-- Closed-box determinant convergence is fully uniform, not merely pointwise. -/
theorem taylorPartialSum_det_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        |(continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))).det -
          (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q (fun A : V →L[ℝ] V => A.det)
      ContinuousLinearMap.continuous_det a degree ha hdegree box

/-- Finite operator polynomials converge uniformly on the full closed box. -/
theorem taylorPartialSum_polynomial_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        ‖continuousLinearMapPolynomial coeff polynomialDegree
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          continuousLinearMapPolynomial coeff polynomialDegree
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon :=
  S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q
    (continuousLinearMapPolynomial coeff polynomialDegree)
    (continuous_continuousLinearMapPolynomial coeff polynomialDegree)
    a degree ha hdegree box

/-- Polynomial traces converge uniformly on the full closed box. -/
theorem taylorPartialSum_polynomialTrace_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        |continuousLinearMapPolynomialTrace coeff polynomialDegree
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          continuousLinearMapPolynomialTrace coeff polynomialDegree
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q
      (continuousLinearMapPolynomialTrace coeff polynomialDegree)
      (continuous_continuousLinearMapPolynomialTrace coeff polynomialDegree)
      a degree ha hdegree box

/-- Polynomial determinants converge uniformly on the full closed box. -/
theorem taylorPartialSum_polynomialDet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        |continuousLinearMapPolynomialDet coeff polynomialDegree
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          continuousLinearMapPolynomialDet coeff polynomialDegree
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q
      (continuousLinearMapPolynomialDet coeff polynomialDegree)
      (continuous_continuousLinearMapPolynomialDet coeff polynomialDegree)
      a degree ha hdegree box

/-- Every finite spectral-moment vector converges uniformly on the full closed
Taylor box. -/
theorem taylorPartialSum_spectralMomentJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (momentOrder : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        ‖continuousLinearMapSpectralMomentJet momentOrder
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          continuousLinearMapSpectralMomentJet momentOrder
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon :=
  S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q
    (continuousLinearMapSpectralMomentJet momentOrder)
    (continuous_continuousLinearMapSpectralMomentJet momentOrder)
    a degree ha hdegree box

/-- Diagonal form: the Taylor degree may depend arbitrarily on the original
filter variable, with no rate relation, for every continuous observable. -/
theorem taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ p, box.Contains p →
        ‖Phi (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) -
          Phi (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon :=
  S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q Phi hPhi
    (fun a => a) degree tendsto_id hdegree box

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D