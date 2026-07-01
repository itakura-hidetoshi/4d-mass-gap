import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped BigOperators InnerProductSpace LinearPMap

namespace ContinuousLinearMap

variable {ι E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise convergence of a uniformly operator-norm-bounded family of
continuous linear endomorphisms propagates to every finite operator power. -/
theorem tendsto_pow_apply_of_pointwise_of_uniform_opNorm_le
    (l : Filter ι)
    (A : ι → E →L[ℝ] E)
    (R : E →L[ℝ] E)
    (K : ℝ)
    (hA : ∀ i, ‖A i‖ ≤ K)
    (hPoint : ∀ x : E, Tendsto (fun i => A i x) l (𝓝 (R x))) :
    ∀ n : ℕ, ∀ x : E,
      Tendsto (fun i => ((A i) ^ n) x) l (𝓝 ((R ^ n) x)) := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x))
  | succ n ih =>
      intro x
      let v : E := (R ^ n) x
      have hIter : Tendsto (fun i => ((A i) ^ n) x) l (𝓝 v) := by
        simpa [v] using ih x
      have hDiff :
          Tendsto (fun i => ((A i) ^ n) x - v) l (𝓝 0) := by
        simpa using hIter.sub
          (tendsto_const_nhds : Tendsto (fun _ : ι => v) l (𝓝 v))
      have hMajorant :
          Tendsto (fun i => K * ‖((A i) ^ n) x - v‖) l (𝓝 0) := by
        have hK : Tendsto (fun _ : ι => K) l (𝓝 K) := tendsto_const_nhds
        simpa using hK.mul hDiff.norm
      have hVariable :
          Tendsto (fun i => A i (((A i) ^ n) x - v)) l (𝓝 0) := by
        apply squeeze_zero_norm'
        · exact Eventually.of_forall fun i =>
            (A i).le_of_opNorm_le (hA i) (((A i) ^ n) x - v)
        · exact hMajorant
      have hFixed : Tendsto (fun i => A i v) l (𝓝 (R v)) :=
        hPoint v
      have hSum := hVariable.add hFixed
      simpa [v, pow_succ', map_sub] using hSum

/-- Finite real linear combinations of operator powers inherit pointwise
convergence from a uniformly bounded strongly convergent operator family. -/
theorem tendsto_finset_sum_smul_pow_apply_of_pointwise_of_uniform_opNorm_le
    (l : Filter ι)
    (A : ι → E →L[ℝ] E)
    (R : E →L[ℝ] E)
    (K : ℝ)
    (hA : ∀ i, ‖A i‖ ≤ K)
    (hPoint : ∀ x : E, Tendsto (fun i => A i x) l (𝓝 (R x)))
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (x : E) :
    Tendsto
      (fun i => ∑ n in s, c n • (((A i) ^ n) x))
      l
      (𝓝 (∑ n in s, c n • ((R ^ n) x))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ι => (0 : E)) l (𝓝 0))
  | @insert n s hn ih =>
      have hPower :=
        tendsto_pow_apply_of_pointwise_of_uniform_opNorm_le
          l A R K hA hPoint n x
      have hTerm := hPower.const_smul (c n)
      simpa [Finset.sum_insert, hn] using hTerm.add ih

end ContinuousLinearMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every finite power of the bounded rescaled-defect resolvent converges
strongly to the corresponding power of the continuum Hamiltonian resolvent. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_pow_tendsto_continuumResolvent_pow
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ((G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda) ^ n) y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (((G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda) ^ n) y)) := by
  let A : G.AdmissibleRescaledDefectTime →
      P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    fun tau => G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau hlambda
  let R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf hlambda
  let K : ℝ := (G.mass / 2 - lambda)⁻¹
  have hNorm : ∀ tau, ‖A tau‖ ≤ K := by
    intro tau
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau)
        hlambda
  have hPoint : ∀ x : P.VacuumOrthogonalHilbert,
      Tendsto (fun tau => A tau x)
        G.admissibleRescaledDefectTimeFilter (𝓝 (R x)) := by
    intro x
    simpa [A, R] using
      G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
        T hP hInnerSymmetric hSelf hlambda x
  simpa [A, R] using
    ContinuousLinearMap.tendsto_pow_apply_of_pointwise_of_uniform_opNorm_le
      G.admissibleRescaledDefectTimeFilter A R K hNorm hPoint n y

/-- Equivalent norm formulation for convergence of finite resolvent powers. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_pow_sub_continuumResolvent_pow_norm_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ‖((G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda) ^ n) y -
          ((G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda) ^ n) y‖)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  have hPow :=
    G.admissibleRescaledDefectResolvent_pow_tendsto_continuumResolvent_pow
      T hP hInnerSymmetric hSelf hlambda n y
  have hConst :
      Tendsto
        (fun _ : G.AdmissibleRescaledDefectTime =>
          ((G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda) ^ n) y)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (((G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda) ^ n) y)) :=
    tendsto_const_nhds
  have hSub := hPow.sub hConst
  simpa using hSub.norm

/-- Every finite real polynomial in the bounded rescaled-defect resolvent
converges strongly to the same polynomial in the continuum resolvent. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finsetPolynomial_tendsto_continuumResolvent_finsetPolynomial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ∑ n in s, c n •
          (((G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda) ^ n) y))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (∑ n in s, c n •
          (((G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda) ^ n) y))) := by
  let A : G.AdmissibleRescaledDefectTime →
      P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    fun tau => G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau hlambda
  let R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf hlambda
  let K : ℝ := (G.mass / 2 - lambda)⁻¹
  have hNorm : ∀ tau, ‖A tau‖ ≤ K := by
    intro tau
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau)
        hlambda
  have hPoint : ∀ x : P.VacuumOrthogonalHilbert,
      Tendsto (fun tau => A tau x)
        G.admissibleRescaledDefectTimeFilter (𝓝 (R x)) := by
    intro x
    simpa [A, R] using
      G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
        T hP hInnerSymmetric hSelf hlambda x
  simpa [A, R] using
    ContinuousLinearMap.tendsto_finset_sum_smul_pow_apply_of_pointwise_of_uniform_opNorm_le
      G.admissibleRescaledDefectTimeFilter A R K hNorm hPoint s c y

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
