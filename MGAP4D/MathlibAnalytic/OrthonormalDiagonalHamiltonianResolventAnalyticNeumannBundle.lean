import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventFactorialDerivativeBundle
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1200000

/-- The distance-to-gap ball around a sub-gap parameter makes the normalized
resolvent perturbation strictly contractive in operator norm. -/
theorem orthonormalDiagonalHamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    ‖(mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda‖ < 1 := by
  have hgap : 0 < delta - lambda := sub_pos.mpr hlambda
  have hR :=
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta lambda hdelta hlambda
  calc
    ‖(mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
      ‖mu - lambda‖ *
        ‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ :=
      ContinuousLinearMap.opNorm_smul_le
        (mu - lambda)
        (orthonormalDiagonalHamiltonianResolvent b a lambda)
    _ ≤ ‖mu - lambda‖ * (delta - lambda)⁻¹ :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg (mu - lambda))
    _ < (delta - lambda) * (delta - lambda)⁻¹ :=
      mul_lt_mul_of_pos_right hdist (inv_pos.mpr hgap)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hgap)

/-- Exact local inverse representation of the real resolvent whenever the
normalized parameter perturbation has norm strictly below one. -/
theorem orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta) (hmu : mu < delta)
    (hsmall :
      ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ < 1) :
    orthonormalDiagonalHamiltonianResolvent b a mu =
      Ring.inverse
          (1 - (mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) *
        orthonormalDiagonalHamiltonianResolvent b a lambda := by
  let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
  let Rmu := orthonormalDiagonalHamiltonianResolvent b a mu
  let perturb : E →L[ℝ] E := (mu - lambda) • Rlambda
  change Rmu = Ring.inverse (1 - perturb) * Rlambda
  have hid :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu) := by
    simpa [Rlambda, Rmu] using
      (orthonormalDiagonalHamiltonianResolvent_sub_eq_smul_mul
        b a delta hdelta hlambda hmu)
  have hneg :
      (lambda - mu) • (Rlambda * Rmu) =
        -((mu - lambda) • (Rlambda * Rmu)) := by
    calc
      (lambda - mu) • (Rlambda * Rmu) =
          (-(mu - lambda)) • (Rlambda * Rmu) := by
        congr 1
        ring
      _ = -((mu - lambda) • (Rlambda * Rmu)) := by
        exact neg_smul (mu - lambda) (Rlambda * Rmu)
  have hid' :
      Rmu - (mu - lambda) • (Rlambda * Rmu) = Rlambda := by
    rw [sub_eq_add_neg, ← hneg, ← hid]
    abel
  have hmul : (1 - perturb) * Rmu = Rlambda := by
    apply ContinuousLinearMap.ext
    intro y
    have hidApply := congrArg (fun A : E →L[ℝ] E => A y) hid'
    simpa [perturb, ContinuousLinearMap.mul_def] using hidApply
  rw [NormedRing.inverse_one_sub perturb hsmall]
  let u := Units.oneSub perturb hsmall
  change Rmu = (↑u⁻¹ : E →L[ℝ] E) * Rlambda
  symm
  calc
    (↑u⁻¹ : E →L[ℝ] E) * Rlambda =
        (↑u⁻¹ : E →L[ℝ] E) * ((1 - perturb) * Rmu) := by
      rw [hmul]
    _ = (↑u⁻¹ : E →L[ℝ] E) *
        ((↑u : E →L[ℝ] E) * Rmu) := by
      simp [u]
    _ = Rmu := by
      rw [← mul_assoc]
      simp

/-- Exact local inverse representation on the full distance-to-gap ball around
any sub-gap center.  The ball condition itself implies that the target
parameter remains below the gap. -/
theorem orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    orthonormalDiagonalHamiltonianResolvent b a mu =
      Ring.inverse
          (1 - (mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) *
        orthonormalDiagonalHamiltonianResolvent b a lambda := by
  have hdistAbs : |mu - lambda| < delta - lambda := by
    simpa only [Real.norm_eq_abs] using hdist
  have hmu : mu < delta := by
    have hle : mu - lambda ≤ |mu - lambda| := le_abs_self (mu - lambda)
    linarith
  exact orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul
    b a delta hdelta hlambda hmu
      (orthonormalDiagonalHamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
        b a delta hdelta hlambda hdist)

/-- Exact finite Neumann expansion with an ordered remainder term on every
sub-gap distance ball.  No commutativity assumption is used. -/
theorem orthonormalDiagonalHamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    orthonormalDiagonalHamiltonianResolvent b a mu =
      (∑ i ∈ Finset.range N,
          ((mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) ^ i) *
        orthonormalDiagonalHamiltonianResolvent b a lambda +
      ((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N *
        orthonormalDiagonalHamiltonianResolvent b a mu := by
  let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
  let Rmu := orthonormalDiagonalHamiltonianResolvent b a mu
  let perturb : E →L[ℝ] E := (mu - lambda) • Rlambda
  change Rmu =
    (∑ i ∈ Finset.range N, perturb ^ i) * Rlambda + perturb ^ N * Rmu
  have hsmall : ‖perturb‖ < 1 := by
    simpa [perturb, Rlambda] using
      (orthonormalDiagonalHamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
        b a delta hdelta hlambda hdist)
  have hlocal : Rmu = Ring.inverse (1 - perturb) * Rlambda := by
    simpa [perturb, Rlambda, Rmu] using
      (orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
        b a delta hdelta hlambda hdist)
  calc
    Rmu = Ring.inverse (1 - perturb) * Rlambda := hlocal
    _ = ((∑ i ∈ Finset.range N, perturb ^ i) +
          perturb ^ N * Ring.inverse (1 - perturb)) * Rlambda := by
      exact congrArg (fun A : E →L[ℝ] E => A * Rlambda)
        (NormedRing.inverse_one_sub_nth_order' N hsmall)
    _ = (∑ i ∈ Finset.range N, perturb ^ i) * Rlambda +
        perturb ^ N * (Ring.inverse (1 - perturb) * Rlambda) := by
      noncomm_ring
    _ = (∑ i ∈ Finset.range N, perturb ^ i) * Rlambda +
        perturb ^ N * Rmu := by
      rw [← hlocal]

/-- The finite-dimensional orthonormal-diagonal real resolvent is real analytic
at every parameter strictly below the common spectral gap. -/
theorem orthonormalDiagonalHamiltonianResolvent_analyticAt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda : ℝ} (hlambda : lambda < delta) :
    AnalyticAt ℝ (orthonormalDiagonalHamiltonianResolvent b a) lambda := by
  with_reducible_and_instances
    let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
    let perturb : ℝ → (E →L[ℝ] E) :=
      fun mu => (mu - lambda) • Rlambda
    let candidate : ℝ → (E →L[ℝ] E) :=
      fun mu => Ring.inverse (1 - perturb mu) * Rlambda
    have hscalar : AnalyticAt ℝ (fun mu : ℝ => mu - lambda) lambda :=
      analyticAt_id.sub analyticAt_const
    have hconstant : AnalyticAt ℝ (fun _ : ℝ => Rlambda) lambda :=
      analyticAt_const
    letI : IsBoundedSMul ℝ (E →L[ℝ] E) :=
      IsBoundedSMul.of_norm_smul_le fun r A =>
        ContinuousLinearMap.opNorm_smul_le r A
    have hperturb : AnalyticAt ℝ perturb lambda := by
      change AnalyticAt ℝ (fun mu : ℝ => (mu - lambda) • Rlambda) lambda
      exact hscalar.smul hconstant
    have hperturbZero : perturb lambda = 0 := by
      dsimp [perturb]
      module
    have hinverse :
        AnalyticAt ℝ (fun mu => Ring.inverse (1 - perturb mu)) lambda := by
      have houter :
          AnalyticAt ℝ (fun R : E →L[ℝ] E => Ring.inverse (1 - R))
            (perturb lambda) := by
        rw [hperturbZero]
        exact analyticAt_inverse_one_sub ℝ (E →L[ℝ] E)
      simpa only [Function.comp_def] using houter.comp hperturb
    have hcandidate : AnalyticAt ℝ candidate lambda := by
      have hmul :
          AnalyticAt ℝ
            (fun mu => Ring.inverse (1 - perturb mu) * Rlambda) lambda :=
        AnalyticAt.mul (𝕜 := ℝ) (A := E →L[ℝ] E) hinverse hconstant
      simpa only [candidate] using hmul
    have hsmall : ∀ᶠ mu in 𝓝 lambda, ‖perturb mu‖ < 1 := by
      have hboundContinuous :
          ContinuousAt (fun mu : ℝ => ‖mu - lambda‖ * ‖Rlambda‖) lambda := by
        fun_prop
      have hboundAt : ‖lambda - lambda‖ * ‖Rlambda‖ < (1 : ℝ) := by
        simp
      have hbound :
          ∀ᶠ mu in 𝓝 lambda, ‖mu - lambda‖ * ‖Rlambda‖ < 1 := by
        simpa only [Set.mem_Iio] using
          hboundContinuous.eventually_mem (Iio_mem_nhds hboundAt)
      filter_upwards [hbound] with mu hmu
      change ‖(mu - lambda) • Rlambda‖ < 1
      exact (ContinuousLinearMap.opNorm_smul_le (mu - lambda) Rlambda).trans_lt hmu
    have heq :
        candidate =ᶠ[𝓝 lambda]
          orthonormalDiagonalHamiltonianResolvent b a := by
      filter_upwards [hsmall, Iio_mem_nhds hlambda] with mu hmuSmall hmu
      simpa only [candidate, perturb, Rlambda] using
        (orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul
          b a delta hdelta hlambda hmu hmuSmall).symm
    exact hcandidate.congr heq

/-- Real analyticity of the orthonormal-diagonal resolvent on a neighborhood of
every point of the full open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_analyticOnNhd
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    AnalyticOnNhd ℝ
      (orthonormalDiagonalHamiltonianResolvent b a) (Set.Iio delta) := by
  intro lambda hlambda
  exact orthonormalDiagonalHamiltonianResolvent_analyticAt
    b a delta hdelta hlambda

/-- Within-set real analyticity of the orthonormal-diagonal resolvent on the
full open sub-gap interval. -/
theorem orthonormalDiagonalHamiltonianResolvent_analyticOn
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    AnalyticOn ℝ
      (orthonormalDiagonalHamiltonianResolvent b a) (Set.Iio delta) :=
  (orthonormalDiagonalHamiltonianResolvent_analyticOnNhd
    b a delta hdelta).analyticOn

/-- Analyticity, exact local inverse representation, and the finite ordered
Neumann expansion with exact remainder as one package. -/
theorem orthonormalDiagonalHamiltonianResolventAnalyticNeumann_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    AnalyticOnNhd ℝ
        (orthonormalDiagonalHamiltonianResolvent b a) (Set.Iio delta) ∧
      AnalyticOn ℝ
        (orthonormalDiagonalHamiltonianResolvent b a) (Set.Iio delta) ∧
      ∀ {lambda mu : ℝ} (hlambda : lambda < delta)
          (hdist : ‖mu - lambda‖ < delta - lambda),
        orthonormalDiagonalHamiltonianResolvent b a mu =
            Ring.inverse
                (1 - (mu - lambda) •
                  orthonormalDiagonalHamiltonianResolvent b a lambda) *
              orthonormalDiagonalHamiltonianResolvent b a lambda ∧
          ∀ N : ℕ,
            orthonormalDiagonalHamiltonianResolvent b a mu =
              (∑ i ∈ Finset.range N,
                  ((mu - lambda) •
                    orthonormalDiagonalHamiltonianResolvent b a lambda) ^ i) *
                orthonormalDiagonalHamiltonianResolvent b a lambda +
              ((mu - lambda) •
                  orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N *
                orthonormalDiagonalHamiltonianResolvent b a mu := by
  refine ⟨orthonormalDiagonalHamiltonianResolvent_analyticOnNhd
      b a delta hdelta,
    orthonormalDiagonalHamiltonianResolvent_analyticOn
      b a delta hdelta, ?_⟩
  intro lambda mu hlambda hdist
  exact ⟨orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
      b a delta hdelta hlambda hdist,
    fun N =>
      orthonormalDiagonalHamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
        b a delta hdelta N hlambda hdist⟩

end MathlibAnalytic
end MGAP4D

end
