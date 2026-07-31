import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorStrongLimitUpgradeBundle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 2400000

/-- Abstract resolvent calculus on an open real half-line.  The only analytic
input is operator-norm continuity; the resolvent identity then generates every
ordinary derivative with the exact factorial coefficient. -/
structure ContinuousLinearMapOpenResolventData
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  gap : ℝ
  resolvent : ℝ → E →L[ℝ] E
  continuousOn : ContinuousOn resolvent (Set.Iio gap)
  resolvent_identity : ∀ {lambda mu : ℝ}, lambda < gap → mu < gap →
    resolvent lambda - resolvent mu =
      (lambda - mu) • ((resolvent lambda).comp (resolvent mu))

namespace ContinuousLinearMapOpenResolventData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first derivative of an abstract open resolvent is its square. -/
theorem hasDerivWithinAt (D : ContinuousLinearMapOpenResolventData E)
    {lambda : ℝ} (hlambda : lambda < D.gap) :
    HasDerivWithinAt D.resolvent
      ((D.resolvent lambda).comp (D.resolvent lambda))
      (Set.Iio D.gap) lambda := by
  refine (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ) (f := D.resolvent)
    (f' := (D.resolvent lambda).comp (D.resolvent lambda))
    (s := Set.Iio D.gap) (x := lambda)).2 ?_
  let Rlambda := D.resolvent lambda
  have hres0 : Tendsto D.resolvent (𝓝[Set.Iio D.gap] lambda)
      (𝓝 (D.resolvent lambda)) := D.continuousOn lambda hlambda
  have hres : Tendsto D.resolvent (𝓝[Set.Iio D.gap] lambda)
      (𝓝 Rlambda) := by simpa [Rlambda] using hres0
  have hres' : Tendsto D.resolvent
      (𝓝[Set.Iio D.gap \ {lambda}] lambda) (𝓝 Rlambda) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro mu hmu
      exact hmu.1
  have hmul : Tendsto (fun mu => D.resolvent mu * Rlambda)
      (𝓝[Set.Iio D.gap \ {lambda}] lambda)
      (𝓝 (Rlambda * Rlambda)) := hres'.mul tendsto_const_nhds
  have hproduct : Tendsto (fun mu => D.resolvent mu * Rlambda)
      (𝓝[Set.Iio D.gap \ {lambda}] lambda)
      (𝓝 (Rlambda.comp Rlambda)) := by simpa using hmul
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with mu hmu
  rcases hmu with ⟨hmuGap, hmuNe⟩
  have hne : mu - lambda ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hmuNe
  rw [slope_def_module, D.resolvent_identity hmuGap hlambda,
    inv_smul_smul₀ hne]

/-- Ordinary first derivative formula on the open half-line. -/
theorem hasDerivAt (D : ContinuousLinearMapOpenResolventData E)
    {lambda : ℝ} (hlambda : lambda < D.gap) :
    HasDerivAt D.resolvent
      ((D.resolvent lambda).comp (D.resolvent lambda)) lambda := by
  exact (D.hasDerivWithinAt hlambda).hasDerivAt (Iio_mem_nhds hlambda)

/-- The abstract resolvent is differentiable throughout its open domain. -/
theorem differentiableOn (D : ContinuousLinearMapOpenResolventData E) :
    DifferentiableOn ℝ D.resolvent (Set.Iio D.gap) := by
  intro lambda hlambda
  exact (D.hasDerivWithinAt hlambda).differentiableWithinAt

/-- The `k`-th composition power has derivative `k • R^(k+1)`. -/
theorem pow_hasDerivWithinAt (D : ContinuousLinearMapOpenResolventData E)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < D.gap) :
    HasDerivWithinAt (fun mu => (D.resolvent mu) ^ k)
      ((k : ℝ) • (D.resolvent lambda) ^ (k + 1))
      (Set.Iio D.gap) lambda := by
  induction k with
  | zero =>
      simpa using hasDerivWithinAt_const
        (x := lambda) (s := Set.Iio D.gap) (c := (1 : E →L[ℝ] E))
  | succ k ih =>
      have hR : HasDerivWithinAt D.resolvent
          ((D.resolvent lambda) ^ 2) (Set.Iio D.gap) lambda := by
        simpa [pow_two, ContinuousLinearMap.mul_def] using D.hasDerivWithinAt hlambda
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ) (𝔸 := E →L[ℝ] E) ih hR
      have hmul' : HasDerivWithinAt
          (fun mu => (D.resolvent mu) ^ (k + 1))
          ((k : ℝ) • (D.resolvent lambda) ^ (k + 1) * D.resolvent lambda +
            (D.resolvent lambda) ^ k * (D.resolvent lambda) ^ 2)
          (Set.Iio D.gap) lambda := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          ((k : ℝ) • (D.resolvent lambda) ^ (k + 1) * D.resolvent lambda +
            (D.resolvent lambda) ^ k * (D.resolvent lambda) ^ 2) =
          ((Nat.succ k : ℕ) : ℝ) •
            (D.resolvent lambda) ^ (Nat.succ k + 1) := by
        let Rlambda := D.resolvent lambda
        change ((k : ℝ) • Rlambda ^ (k + 1)) * Rlambda +
            Rlambda ^ k * Rlambda ^ 2 =
          ((Nat.succ k : ℕ) : ℝ) • Rlambda ^ (Nat.succ k + 1)
        rw [Algebra.smul_mul_assoc]
        have hfirst : Rlambda ^ (k + 1) * Rlambda = Rlambda ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ Rlambda (k + 1)).symm
        have hsecond : Rlambda ^ k * Rlambda ^ 2 = Rlambda ^ (k + 2) := by
          simpa using (pow_add Rlambda k 2).symm
        rw [hfirst, hsecond]
        calc
          (k : ℝ) • Rlambda ^ (k + 2) + Rlambda ^ (k + 2) =
              (k : ℝ) • Rlambda ^ (k + 2) +
                (1 : ℝ) • Rlambda ^ (k + 2) := by rw [one_smul ℝ]
          _ = ((k : ℝ) + 1) • Rlambda ^ (k + 2) :=
            (add_smul (k : ℝ) (1 : ℝ) _).symm
          _ = ((Nat.succ k : ℕ) : ℝ) •
              Rlambda ^ (Nat.succ k + 1) := by rw [Nat.cast_succ]
      rw [hderiv] at hmul'
      exact hmul'

/-- The abstract resolvent is `Cⁿ` for every finite order. -/
theorem contDiffOn_nat (D : ContinuousLinearMapOpenResolventData E) (n : ℕ) :
    ContDiffOn ℝ n D.resolvent (Set.Iio D.gap) := by
  induction n with
  | zero => exact (contDiffOn_zero (𝕜 := ℝ)).2 D.continuousOn
  | succ n ih =>
      apply (contDiffOn_succ_iff_deriv_of_isOpen
        (n := (n : ℕ∞ω)) isOpen_Iio).2
      refine ⟨D.differentiableOn, ?_, ?_⟩
      · intro lambda hlambda
        simpa [pow_two, ContinuousLinearMap.mul_def] using
          (D.hasDerivAt hlambda).deriv
      · exact ih.clm_comp ih

/-- The abstract resolvent is smooth on the whole open half-line. -/
theorem contDiffOn_infty (D : ContinuousLinearMapOpenResolventData E) :
    ContDiffOn ℝ ∞ D.resolvent (Set.Iio D.gap) :=
  contDiffOn_infty.2 fun n => D.contDiffOn_nat n

/-- Exact factorial formula for all within-derivatives. -/
theorem iteratedDerivWithin (D : ContinuousLinearMapOpenResolventData E)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < D.gap) :
    iteratedDerivWithin n D.resolvent (Set.Iio D.gap) lambda =
      (n.factorial : ℝ) • (D.resolvent lambda) ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin (iteratedDerivWithin n D.resolvent (Set.Iio D.gap))
              (Set.Iio D.gap) lambda =
            derivWithin (fun mu =>
              (n.factorial : ℝ) • (D.resolvent mu) ^ (n + 1))
              (Set.Iio D.gap) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hpow := D.pow_hasDerivWithinAt (n + 1) hlambda
      have hscaled : HasDerivWithinAt
          (fun mu => (n.factorial : ℝ) • (D.resolvent mu) ^ (n + 1))
          ((n.factorial : ℝ) •
            (((n + 1 : ℕ) : ℝ) • (D.resolvent lambda) ^ (n + 2)))
          (Set.Iio D.gap) lambda := by
        simpa only [Pi.smul_apply] using
          (HasDerivWithinAt.const_smul
            (𝕜 := ℝ) (R := ℝ) (F := E →L[ℝ] E)
            (n.factorial : ℝ) hpow)
      let derivValue : E →L[ℝ] E :=
        (n.factorial : ℝ) •
          (((n + 1 : ℕ) : ℝ) • (D.resolvent lambda) ^ (n + 2))
      have hfscaled : HasFDerivWithinAt
          (fun mu => (n.factorial : ℝ) • (D.resolvent mu) ^ (n + 1))
          (toSpanSingleton ℝ derivValue) (Set.Iio D.gap) lambda := by
        simpa [derivValue] using hscaled.hasFDerivWithinAt
      have hfderiv :
          fderivWithin ℝ
              (fun mu => (n.factorial : ℝ) • (D.resolvent mu) ^ (n + 1))
              (Set.Iio D.gap) lambda =
            toSpanSingleton ℝ derivValue :=
        hfscaled.fderivWithin (isOpen_Iio.uniqueDiffOn lambda hlambda)
      have hscaledDeriv :
          derivWithin
              (fun mu => (n.factorial : ℝ) • (D.resolvent mu) ^ (n + 1))
              (Set.Iio D.gap) lambda = derivValue := by
        unfold derivWithin
        rw [hfderiv]
        simp [derivValue]
      rw [hscaledDeriv]
      simp [derivValue, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        smul_smul, mul_comm, Nat.add_assoc]

/-- Exact ordinary all-order derivative formula. -/
theorem iteratedDeriv (D : ContinuousLinearMapOpenResolventData E)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < D.gap) :
    _root_.iteratedDeriv n D.resolvent lambda =
      (n.factorial : ℝ) • (D.resolvent lambda) ^ (n + 1) := by
  calc
    _root_.iteratedDeriv n D.resolvent lambda =
        iteratedDerivWithin n D.resolvent (Set.Iio D.gap) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n) (f := D.resolvent) isOpen_Iio hlambda).symm
    _ = (n.factorial : ℝ) • (D.resolvent lambda) ^ (n + 1) :=
      D.iteratedDerivWithin n hlambda

/-- Filter-indexed Taylor strong-limit data.  This generalizes the sequence-only
interface used by the finite Wilson Taylor layer. -/
structure TaylorStrongLimitDataOn
    {α : Type*} (l : Filter α)
    (F : α → ℝ → E →L[ℝ] E) where
  limitResolvent : ℝ → E →L[ℝ] E
  value_tendsto_apply : ∀ mu : ℝ, ∀ x : E,
    Tendsto (fun a => F a mu x) l (𝓝 (limitResolvent mu x))
  iteratedDeriv_tendsto_apply : ∀ k : ℕ, ∀ lambda : ℝ, ∀ x : E,
    Tendsto (fun a => (_root_.iteratedDeriv k (F a) lambda) x) l
      (𝓝 ((_root_.iteratedDeriv k limitResolvent lambda) x))

/-- Exact factorial derivative formulas and strong convergence of every
resolvent power construct full Taylor strong-limit data. -/
noncomputable def TaylorStrongLimitDataOn.of_resolventPowers
    {α : Type*} {l : Filter α}
    {F : α → ℝ → E →L[ℝ] E} {R : ℝ → E →L[ℝ] E}
    (hValue : ∀ mu : ℝ, ∀ x : E,
      Tendsto (fun a => F a mu x) l (𝓝 (R mu x)))
    (hPower : ∀ k : ℕ, ∀ lambda : ℝ, ∀ x : E,
      Tendsto (fun a => ((F a lambda) ^ (k + 1)) x) l
        (𝓝 (((R lambda) ^ (k + 1)) x)))
    (hDerivF : ∀ a : α, ∀ k : ℕ, ∀ lambda : ℝ,
      _root_.iteratedDeriv k (F a) lambda =
        (k.factorial : ℝ) • (F a lambda) ^ (k + 1))
    (hDerivR : ∀ k : ℕ, ∀ lambda : ℝ,
      _root_.iteratedDeriv k R lambda =
        (k.factorial : ℝ) • (R lambda) ^ (k + 1)) :
    TaylorStrongLimitDataOn l F where
  limitResolvent := R
  value_tendsto_apply := hValue
  iteratedDeriv_tendsto_apply k lambda x := by
    have hp := (hPower k lambda x).const_smul (k.factorial : ℝ)
    simpa only [hDerivF, hDerivR, ContinuousLinearMap.smul_apply] using hp

end ContinuousLinearMapOpenResolventData

end MathlibAnalytic
end MGAP4D
