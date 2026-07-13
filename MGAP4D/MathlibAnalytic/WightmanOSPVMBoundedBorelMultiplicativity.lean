import MGAP4D.MathlibAnalytic.WightmanOSPVMSimpleMultiplicativity
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- Pointwise multiplication in the bounded-Borel multiplier layer. -/
def pvmBoundedBorelMul
    (F G : PVMBoundedBorelRealFunction) : PVMBoundedBorelRealFunction where
  toFun := fun energy => F.toFun energy * G.toFun energy
  measurable_toFun := F.measurable_toFun.mul G.measurable_toFun
  bounded_toFun := by
    obtain ⟨CF, hCF⟩ := F.bounded_toFun
    obtain ⟨CG, hCG⟩ := G.bounded_toFun
    have hCFnonneg : 0 ≤ CF :=
      le_trans (norm_nonneg (F.toFun 0)) (hCF 0)
    refine ⟨CF * CG, ?_⟩
    intro energy
    rw [norm_mul]
    exact mul_le_mul (hCF energy) (hCG energy)
      (norm_nonneg (G.toFun energy)) hCFnonneg

@[simp] theorem pvmBoundedBorelMul_apply
    (F G : PVMBoundedBorelRealFunction) (energy : ℝ) :
    (pvmBoundedBorelMul F G).toFun energy =
      F.toFun energy * G.toFun energy :=
  rfl

/-- Multiplying the canonical floor-grid simple approximations gives a uniform
simple approximation of the pointwise product. -/
noncomputable def explicitBoundedBorelCanonicalMulUniformApproximation
    (F G : PVMBoundedBorelRealFunction) :
    ExplicitBoundedBorelSimpleUniformApproximation (pvmBoundedBorelMul F G) where
  simple := fun n =>
    pvmSimpleFuncMul
      (explicitBoundedBorelSimpleApproximation F n)
      (explicitBoundedBorelSimpleApproximation G n)
  uniform_tendsto := by
    obtain ⟨CF, hCF⟩ := F.bounded_toFun
    obtain ⟨CG, hCG⟩ := G.bounded_toFun
    have hCFnonneg : 0 ≤ CF :=
      le_trans (norm_nonneg (F.toFun 0)) (hCF 0)
    have hCGnonneg : 0 ≤ CG :=
      le_trans (norm_nonneg (G.toFun 0)) (hCG 0)
    intro ε hε
    let D : ℝ := CF + CG + 2
    have hD : 0 < D := by
      dsimp [D]
      linarith
    have hRate :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hEventually :
        ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / D :=
      (tendsto_order.1 hRate).2 (ε / D) (div_pos hε hD)
    rcases eventually_atTop.1 hEventually with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn energy
    let r : ℝ := 1 / ((n : ℝ) + 1)
    have hdenom : 0 < (n : ℝ) + 1 := by positivity
    have hrpos : 0 < r := by
      dsimp [r]
      positivity
    have hrle : r ≤ 1 := by
      dsimp [r]
      apply (div_le_iff₀ hdenom).2
      nlinarith
    have hFerror :
        ‖explicitBoundedBorelSimpleApproximation F n energy -
            F.toFun energy‖ < r := by
      simpa [r] using
        explicitBoundedBorelSimpleApproximation_error_lt F n energy
    have hGerror :
        ‖explicitBoundedBorelSimpleApproximation G n energy -
            G.toFun energy‖ < r := by
      simpa [r] using
        explicitBoundedBorelSimpleApproximation_error_lt G n energy
    have hGapprox :
        ‖explicitBoundedBorelSimpleApproximation G n energy‖ ≤ CG + 1 := by
      calc
        ‖explicitBoundedBorelSimpleApproximation G n energy‖ =
            ‖G.toFun energy +
              (explicitBoundedBorelSimpleApproximation G n energy -
                G.toFun energy)‖ := by
              congr 1
              ring
        _ ≤ ‖G.toFun energy‖ +
            ‖explicitBoundedBorelSimpleApproximation G n energy -
              G.toFun energy‖ := norm_add_le _ _
        _ ≤ CG + r :=
          add_le_add (hCG energy) hGerror.le
        _ ≤ CG + 1 := add_le_add_left hrle CG
    have hProductError :
        ‖explicitBoundedBorelSimpleApproximation F n energy *
              explicitBoundedBorelSimpleApproximation G n energy -
            F.toFun energy * G.toFun energy‖ ≤
          r * (CG + 1) + CF * r := by
      calc
        ‖explicitBoundedBorelSimpleApproximation F n energy *
              explicitBoundedBorelSimpleApproximation G n energy -
            F.toFun energy * G.toFun energy‖ =
            ‖(explicitBoundedBorelSimpleApproximation F n energy -
                F.toFun energy) *
                explicitBoundedBorelSimpleApproximation G n energy +
              F.toFun energy *
                (explicitBoundedBorelSimpleApproximation G n energy -
                  G.toFun energy)‖ := by
              congr 1
              ring
        _ ≤
            ‖(explicitBoundedBorelSimpleApproximation F n energy -
                F.toFun energy) *
                explicitBoundedBorelSimpleApproximation G n energy‖ +
              ‖F.toFun energy *
                (explicitBoundedBorelSimpleApproximation G n energy -
                  G.toFun energy)‖ := norm_add_le _ _
        _ =
            ‖explicitBoundedBorelSimpleApproximation F n energy -
                F.toFun energy‖ *
              ‖explicitBoundedBorelSimpleApproximation G n energy‖ +
            ‖F.toFun energy‖ *
              ‖explicitBoundedBorelSimpleApproximation G n energy -
                G.toFun energy‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ r * (CG + 1) + CF * r := by
          apply add_le_add
          · exact mul_le_mul hFerror.le hGapprox
              (norm_nonneg _) hrpos.le
          · exact mul_le_mul (hCF energy) hGerror.le
              (norm_nonneg _) hCFnonneg
    have hrD : r * D < ε := by
      calc
        r * D < (ε / D) * D :=
          mul_lt_mul_of_pos_right (by simpa [r] using hN n hn) hD
        _ = ε := by field_simp [hD.ne']
    change
      ‖explicitBoundedBorelSimpleApproximation F n energy *
          explicitBoundedBorelSimpleApproximation G n energy -
        F.toFun energy * G.toFun energy‖ < ε
    exact hProductError.trans_lt <| by
      calc
        r * (CG + 1) + CF * r = r * (CF + CG + 1) := by ring
        _ ≤ r * D := by
          dsimp [D]
          nlinarith [hrpos.le]
        _ < ε := hrD

/-- Completed bounded-Borel PVM integration is multiplicative: pointwise
multiplication of bounded scalar multipliers becomes composition of bounded
operators. -/
theorem pvmBoundedBorelSpectralIntegralOperator_mul
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (F G : PVMBoundedBorelRealFunction) :
    pvmBoundedBorelSpectralIntegralOperator P (pvmBoundedBorelMul F G) =
      (pvmBoundedBorelSpectralIntegralOperator P F).comp
        (pvmBoundedBorelSpectralIntegralOperator P G) := by
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  let B := explicitBoundedBorelCanonicalSimpleUniformApproximation G
  let C := explicitBoundedBorelCanonicalMulUniformApproximation F G
  have hA := A.tendsto_completedOperator P
  have hB := B.tendsto_completedOperator P
  have hPair :
      Tendsto
        (fun n : ℕ =>
          (pvmSimpleFuncSpectralIntegralOperator P (A.simple n),
            pvmSimpleFuncSpectralIntegralOperator P (B.simple n)))
        atTop
        (𝓝 (A.completedOperator P, B.completedOperator P)) :=
    hA.prodMk_nhds hB
  have hComp :
      Tendsto
        (fun n : ℕ =>
          (pvmSimpleFuncSpectralIntegralOperator P (A.simple n)).comp
            (pvmSimpleFuncSpectralIntegralOperator P (B.simple n)))
        atTop
        (𝓝 ((A.completedOperator P).comp (B.completedOperator P))) := by
    have hContinuous :
        Continuous
          (fun p : (H →L[ℝ] H) × (H →L[ℝ] H) => p.1.comp p.2) :=
      (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := H) (F := H) (G := H)).continuous
    exact hContinuous.continuousAt.tendsto.comp hPair
  have hTerm : ∀ n : ℕ,
      pvmSimpleFuncSpectralIntegralOperator P (C.simple n) =
        (pvmSimpleFuncSpectralIntegralOperator P (A.simple n)).comp
          (pvmSimpleFuncSpectralIntegralOperator P (B.simple n)) := by
    intro n
    dsimp [A, B, C,
      explicitBoundedBorelCanonicalSimpleUniformApproximation,
      explicitBoundedBorelCanonicalMulUniformApproximation]
    exact pvmSimpleFuncSpectralIntegralOperator_mul P
      (explicitBoundedBorelSimpleApproximation F n)
      (explicitBoundedBorelSimpleApproximation G n)
  have hCompleted :
      C.completedOperator P =
        (A.completedOperator P).comp (B.completedOperator P) := by
    apply tendsto_nhds_unique (C.tendsto_completedOperator P)
    simpa only [hTerm] using hComp
  rw [C.completedOperator_eq_canonical P,
    A.completedOperator_eq_canonical P,
    B.completedOperator_eq_canonical P] at hCompleted
  exact hCompleted

end

end MathlibAnalytic
end MGAP4D
