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

/-- The common upper spectral edge remains strictly below the gap. -/
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

/-- A finite real polynomial evaluated on a continuous endomorphism. -/
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
  exact (continuousLinearMapTrace (V := V)).continuous.comp
    (continuous_continuousLinearMapPolynomial coeff degree)

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
  exact (continuousLinearMapTrace (V := V)).continuous.comp
    (continuous_id.pow n)

/-- Every finite moment jet is continuous in the supremum norm. -/
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

/-- Uniform convergence in a finite-dimensional normed domain passes through
any continuous observable once the limit family has a common bound. -/
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
      (hA0 i hi).trans (by linarith [hR])
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

/-- Uniform compressed-resolvent bound on a closed subgap half-line. -/
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

/-- Uniform compressed Taylor-derivative bound on a closed subgap half-line. -/
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
    continuousLinearMap_pow_succ_norm_le (D.resolvent lambda) hq0 hres k
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
    _ = ‖Q‖ * ((k.factorial : ℝ) * (D.gap - u)⁻¹ ^ (k + 1)) * ‖J‖ := rfl

end ContinuousLinearMapOpenResolventNormBoundData

end MathlibAnalytic
end MGAP4D
