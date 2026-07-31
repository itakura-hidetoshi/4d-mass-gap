import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteTransfer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Finite vector of scalar Newton weights through a fixed interpolation
degree.  The final entry is exposed recursively. -/
def continuousLinearMapRealResolventNewtonWeightVector :
    (degree : ℕ) → (Fin (degree + 1) → ℝ) → ℝ → Fin (degree + 1) → ℝ
  | 0, _, _ => fun _ => 1
  | n + 1, nodes, z =>
      continuousLinearMapFinAppend
        (continuousLinearMapRealResolventNewtonWeightVector
          n (Fin.init nodes) z)
        (continuousLinearMapRealResolventNewtonNodeProduct
          (n + 1) (Fin.init nodes) z)

@[simp]
theorem continuousLinearMapRealResolventNewtonWeightVector_zero
    (nodes : Fin 1 → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventNewtonWeightVector 0 nodes z =
      fun _ => 1 := rfl

@[simp]
theorem continuousLinearMapRealResolventNewtonWeightVector_succ
    (n : ℕ) (nodes : Fin (n + 2) → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventNewtonWeightVector (n + 1) nodes z =
      continuousLinearMapFinAppend
        (continuousLinearMapRealResolventNewtonWeightVector
          n (Fin.init nodes) z)
        (continuousLinearMapRealResolventNewtonNodeProduct
          (n + 1) (Fin.init nodes) z) := rfl

/-- Recursive common bound for a complete finite Newton-weight vector. -/
def continuousLinearMapRealResolventNewtonWeightEnvelope : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, D =>
      continuousLinearMapRealResolventNewtonWeightEnvelope n D + D ^ (n + 1)

@[simp]
theorem continuousLinearMapRealResolventNewtonWeightEnvelope_zero
    (D : ℝ) :
    continuousLinearMapRealResolventNewtonWeightEnvelope 0 D = 1 := rfl

@[simp]
theorem continuousLinearMapRealResolventNewtonWeightEnvelope_succ
    (n : ℕ) (D : ℝ) :
    continuousLinearMapRealResolventNewtonWeightEnvelope (n + 1) D =
      continuousLinearMapRealResolventNewtonWeightEnvelope n D + D ^ (n + 1) := rfl

/-- Newton-weight envelopes are nonnegative for nonnegative displacement
bounds. -/
theorem continuousLinearMapRealResolventNewtonWeightEnvelope_nonneg
    (degree : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ continuousLinearMapRealResolventNewtonWeightEnvelope degree D := by
  induction degree with
  | zero => simp
  | succ n ih =>
      rw [continuousLinearMapRealResolventNewtonWeightEnvelope_succ]
      exact add_nonneg ih (pow_nonneg hD (n + 1))

/-- A common displacement bound controls the product-supremum norm of the
complete finite Newton-weight vector. -/
theorem continuousLinearMapRealResolventNewtonWeightVector_norm_le
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z D : ℝ)
    (hD : 0 ≤ D) (hnodes : ∀ i, |z - nodes i| ≤ D) :
    ‖continuousLinearMapRealResolventNewtonWeightVector degree nodes z‖ ≤
      continuousLinearMapRealResolventNewtonWeightEnvelope degree D := by
  induction degree with
  | zero =>
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      fin_cases i
      simp
  | succ n ih =>
      have hEnv : 0 ≤
          continuousLinearMapRealResolventNewtonWeightEnvelope n D :=
        continuousLinearMapRealResolventNewtonWeightEnvelope_nonneg n D hD
      have hPow : 0 ≤ D ^ (n + 1) := pow_nonneg hD (n + 1)
      rw [continuousLinearMapRealResolventNewtonWeightEnvelope_succ]
      rw [pi_norm_le_iff_of_nonneg (add_nonneg hEnv hPow)]
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [continuousLinearMapRealResolventNewtonWeightVector_succ,
          continuousLinearMapFinAppend_last, Real.norm_eq_abs]
        exact
          (abs_continuousLinearMapRealResolventNewtonNodeProduct_le
            (n + 1) (Fin.init nodes) z D hD
            (fun j => hnodes j.castSucc)).trans
            (le_add_of_nonneg_left hEnv)
      · simp only [continuousLinearMapRealResolventNewtonWeightVector_succ,
          continuousLinearMapFinAppend_castSucc]
        have hih := ih (Fin.init nodes) (fun j => hnodes j.castSucc)
        rw [pi_norm_le_iff_of_nonneg hEnv] at hih
        exact (hih j).trans (le_add_of_nonneg_right hPow)

/-- Newton-Hermite interpolation with an explicit finite scalar-weight vector. -/
def continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (degree : ℕ) → (Fin (degree + 1) → ℝ) →
      (Fin (degree + 1) → (V →L[ℝ] V)) → (V →L[ℝ] V)
  | 0, weight, R => weight 0 • R 0
  | n + 1, weight, R =>
      continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
          n (Fin.init weight) (Fin.init R) +
        weight (Fin.last (n + 1)) •
          continuousLinearMapRealResolventHermiteObservable (n + 1) R

@[simp]
theorem continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (weight : Fin 1 → ℝ) (R : Fin 1 → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
      0 weight R = weight 0 • R 0 := rfl

@[simp]
theorem continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (weight : Fin (n + 2) → ℝ)
    (R : Fin (n + 2) → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
        (n + 1) weight R =
      continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
          n (Fin.init weight) (Fin.init R) +
        weight (Fin.last (n + 1)) •
          continuousLinearMapRealResolventHermiteObservable (n + 1) R := rfl

/-- The weighted interpolant is continuous jointly in its finite scalar and
operator tuples. -/
theorem continuous_continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∀ degree : ℕ,
      Continuous
        (fun x : (Fin (degree + 1) → ℝ) ×
            (Fin (degree + 1) → (V →L[ℝ] V)) =>
          continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
            degree x.1 x.2)
  | 0 => by
      change Continuous (fun x : (Fin 1 → ℝ) ×
        (Fin 1 → (V →L[ℝ] V)) => x.1 0 • x.2 0)
      fun_prop
  | n + 1 => by
      have hweightInit : Continuous
          (fun x : (Fin (n + 2) → ℝ) ×
              (Fin (n + 2) → (V →L[ℝ] V)) => Fin.init x.1) := by
        apply continuous_pi
        intro i
        exact (continuous_apply i.castSucc).comp continuous_fst
      have hoperatorInit : Continuous
          (fun x : (Fin (n + 2) → ℝ) ×
              (Fin (n + 2) → (V →L[ℝ] V)) => Fin.init x.2) := by
        apply continuous_pi
        intro i
        exact (continuous_apply i.castSucc).comp continuous_snd
      have hinit : Continuous
          (fun x : (Fin (n + 2) → ℝ) ×
              (Fin (n + 2) → (V →L[ℝ] V)) =>
            (Fin.init x.1, Fin.init x.2)) :=
        hweightInit.prod_mk hoperatorInit
      have hlast : Continuous
          (fun x : (Fin (n + 2) → ℝ) ×
              (Fin (n + 2) → (V →L[ℝ] V)) =>
            x.1 (Fin.last (n + 1))) :=
        (continuous_apply (Fin.last (n + 1))).comp continuous_fst
      have hHermite : Continuous
          (fun x : (Fin (n + 2) → ℝ) ×
              (Fin (n + 2) → (V →L[ℝ] V)) =>
            continuousLinearMapRealResolventHermiteObservable (n + 1) x.2) :=
        (continuous_continuousLinearMapRealResolventHermiteObservable
          (V := V) (n + 1)).comp continuous_snd
      exact
        ((continuous_continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
          n).comp hinit).add (hlast.smul hHermite)

/-- The recursive Newton weights recover the original Newton-Hermite
interpolant observable exactly. -/
theorem continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable_weightVector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∀ degree : ℕ, ∀ nodes : Fin (degree + 1) → ℝ, ∀ z : ℝ,
      ∀ R : Fin (degree + 1) → (V →L[ℝ] V),
      continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
          degree
          (continuousLinearMapRealResolventNewtonWeightVector degree nodes z) R =
        continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
          degree nodes z R
  | 0, nodes, z, R => by
      simp [continuousLinearMapRealResolventNewtonHermiteInterpolantObservable]
  | n + 1, nodes, z, R => by
      rw [continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable_succ]
      rw [continuousLinearMapRealResolventNewtonHermiteInterpolantObservable_succ]
      simp only [continuousLinearMapRealResolventNewtonWeightVector_succ,
        Fin.init_continuousLinearMapFinAppend,
        continuousLinearMapFinAppend_last]
      rw [continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable_weightVector
        n (Fin.init nodes) z (Fin.init R)]

/-- Joint weighted observable returning the interpolant and exact remainder. -/
def continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ)
    (x : (Fin (degree + 2) → ℝ) ×
      (Fin (degree + 2) → (V →L[ℝ] V))) :
    Fin 2 → (V →L[ℝ] V) :=
  ![continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
      degree (Fin.init x.1) (Fin.init x.2),
    x.1 (Fin.last (degree + 1)) •
      continuousLinearMapRealResolventHermiteObservable (degree + 1) x.2]

/-- The weighted interpolant/remainder pair is continuous jointly in all
finite scalar and operator coordinates. -/
theorem continuous_continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) :
    Continuous
      (continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
        (V := V) degree) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hweightInit : Continuous
        (fun x : (Fin (degree + 2) → ℝ) ×
            (Fin (degree + 2) → (V →L[ℝ] V)) => Fin.init x.1) := by
      apply continuous_pi
      intro k
      exact (continuous_apply k.castSucc).comp continuous_fst
    have hoperatorInit : Continuous
        (fun x : (Fin (degree + 2) → ℝ) ×
            (Fin (degree + 2) → (V →L[ℝ] V)) => Fin.init x.2) := by
      apply continuous_pi
      intro k
      exact (continuous_apply k.castSucc).comp continuous_snd
    simpa [continuousLinearMapRealResolventWeightedNewtonHermitePairObservable]
      using
        (continuous_continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable
          (V := V) degree).comp (hweightInit.prod_mk hoperatorInit)
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    have hlast : Continuous
        (fun x : (Fin (degree + 2) → ℝ) ×
            (Fin (degree + 2) → (V →L[ℝ] V)) =>
          x.1 (Fin.last (degree + 1))) :=
      (continuous_apply (Fin.last (degree + 1))).comp continuous_fst
    have hHermite : Continuous
        (fun x : (Fin (degree + 2) → ℝ) ×
            (Fin (degree + 2) → (V →L[ℝ] V)) =>
          continuousLinearMapRealResolventHermiteObservable (degree + 1) x.2) :=
      (continuous_continuousLinearMapRealResolventHermiteObservable
        (V := V) (degree + 1)).comp continuous_snd
    simpa [continuousLinearMapRealResolventWeightedNewtonHermitePairObservable]
      using hlast.smul hHermite

/-- Recursive Newton weights specialize the weighted pair to the original
fixed-node interpolant/remainder pair observable. -/
theorem continuousLinearMapRealResolventWeightedNewtonHermitePairObservable_weightVector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : Fin (degree + 2) → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventWeightedNewtonHermitePairObservable degree
        (continuousLinearMapRealResolventNewtonWeightVector
            (degree + 1) (continuousLinearMapFinAppend nodes z) z,
          R) =
      continuousLinearMapRealResolventNewtonHermitePairObservable
        degree nodes z R := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [continuousLinearMapRealResolventWeightedNewtonHermitePairObservable,
      continuousLinearMapRealResolventNewtonWeightVector_succ,
      Fin.init_continuousLinearMapFinAppend]
    exact
      continuousLinearMapRealResolventWeightedNewtonHermiteInterpolantObservable_weightVector
        degree nodes z (Fin.init R)
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [continuousLinearMapRealResolventWeightedNewtonHermitePairObservable,
      continuousLinearMapRealResolventNewtonHermitePairObservable,
      continuousLinearMapRealResolventNewtonHermiteRemainderObservable,
      continuousLinearMapRealResolventNewtonWeightVector_succ]

/-- Uniform componentwise convergence of node-plus-evaluation resolvent tuples
transfers to Newton-Hermite interpolant/remainder pairs even when the node and
evaluation values vary across the family.  A common displacement bound is the
only additional scalar control. -/
theorem finiteDimensional_realResolventNewtonHermitePair_variable_tendsto_uniformOn_of_componentwise
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (degree : ℕ) (nodes : ι → Fin (degree + 1) → ℝ) (eval : ι → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hdist : ∀ i ∈ s, ∀ j, |eval i - nodes i j| ≤ D)
    (R : α → ι → Fin (degree + 2) → (V →L[ℝ] V))
    (R0 : ι → Fin (degree + 2) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ∀ j, ‖R0 i j‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ j, ‖R a i j - R0 i j‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventNewtonHermitePairObservable
            degree (nodes i) (eval i) (R a i) -
          continuousLinearMapRealResolventNewtonHermitePairObservable
            degree (nodes i) (eval i) (R0 i)‖ < epsilon := by
  let weight : ι → Fin (degree + 2) → ℝ := fun i =>
    continuousLinearMapRealResolventNewtonWeightVector
      (degree + 1) (continuousLinearMapFinAppend (nodes i) (eval i)) (eval i)
  let A : α → ι →
      (Fin (degree + 2) → ℝ) ×
        (Fin (degree + 2) → (V →L[ℝ] V)) :=
    fun a i => (weight i, R a i)
  let A0 : ι →
      (Fin (degree + 2) → ℝ) ×
        (Fin (degree + 2) → (V →L[ℝ] V)) :=
    fun i => (weight i, R0 i)
  let W : ℝ :=
    continuousLinearMapRealResolventNewtonWeightEnvelope (degree + 1) D
  have hW : 0 ≤ W :=
    continuousLinearMapRealResolventNewtonWeightEnvelope_nonneg
      (degree + 1) D hD
  have hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ W + M := by
    intro i hi
    have hfullDist : ∀ j : Fin (degree + 2),
        |eval i - continuousLinearMapFinAppend (nodes i) (eval i) j| ≤ D := by
      intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using hD
      · simpa using hdist i hi k
    have hweight : ‖weight i‖ ≤ W := by
      simpa [weight, W] using
        continuousLinearMapRealResolventNewtonWeightVector_norm_le
          (degree + 1) (continuousLinearMapFinAppend (nodes i) (eval i))
          (eval i) D hD hfullDist
    have hoperator : ‖R0 i‖ ≤ M := by
      rw [pi_norm_le_iff_of_nonneg hM]
      exact hR0 i hi
    rw [Prod.norm_def]
    exact max_le
      (hweight.trans (le_add_of_nonneg_right hM))
      (hoperator.trans (le_add_of_nonneg_left hW))
  have hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta := by
    intro eta heta
    have h := hR eta heta
    filter_upwards [h] with a ha
    intro i hi
    have htuple : ‖R a i - R0 i‖ < eta := by
      rw [pi_norm_lt_iff heta]
      intro j
      simpa only [Pi.sub_apply] using ha i hi j
    simpa [A, A0, Prod.norm_def] using htuple
  have htransfer :=
    finiteDimensional_continuousObservable_tendsto_uniformOn
      A A0
      (continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
        (V := V) degree)
      (continuous_continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
        (V := V) degree)
      (W + M) (add_nonneg hW hM) hA0 hA
  intro epsilon hepsilon
  have h := htransfer epsilon hepsilon
  filter_upwards [h] with a ha
  intro i hi
  have ha' := ha i hi
  simpa [A, A0, weight,
    continuousLinearMapRealResolventWeightedNewtonHermitePairObservable_weightVector]
    using ha'

end MathlibAnalytic
end MGAP4D
