import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelQuadraticForm
import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelIndicatorLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- Pointwise multiplication of two Mathlib simple real functions, written on
their canonical common pair refinement. -/
noncomputable def pvmSimpleFuncMul
    (f g : SimpleFunc ℝ ℝ) : SimpleFunc ℝ ℝ :=
  (f.pair g).map (fun p : ℝ × ℝ => p.1 * p.2)

@[simp] theorem pvmSimpleFuncMul_apply
    (f g : SimpleFunc ℝ ℝ) (energy : ℝ) :
    pvmSimpleFuncMul f g energy = f energy * g energy :=
  rfl

/-- On the common pair refinement, composition of the first- and second-
coordinate spectral integrals is the integral of the product coefficient. -/
theorem pvmSimpleFuncPairSpectralIntegralOperator_fst_comp_snd_eq_mul
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) :
    (pvmSimpleFuncPairSpectralIntegralOperator P f g Prod.fst).comp
        (pvmSimpleFuncPairSpectralIntegralOperator P f g Prod.snd) =
      pvmSimpleFuncPairSpectralIntegralOperator P f g
        (fun p : ℝ × ℝ => p.1 * p.2) := by
  ext x
  rw [ContinuousLinearMap.comp_apply,
    pvmSimpleFuncPairSpectralIntegralOperator_apply,
    pvmSimpleFuncPairSpectralIntegralOperator_apply,
    pvmSimpleFuncPairSpectralIntegralOperator_apply]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.smul_sum]
  rw [Finset.sum_eq_single c]
  · rw [P.idempotent]
    simp [smul_smul]
  · intro d hd hdc
    have hDisjoint :
        Disjoint (pvmSimpleFuncPairFiber f g c)
          (pvmSimpleFuncPairFiber f g d) :=
      ((pvmSimpleFuncPairFiber_pairwise_disjoint f g) hdc).symm
    have hZero :
        P.projection (pvmSimpleFuncPairFiber f g c)
            (P.projection (pvmSimpleFuncPairFiber f g d) x) = 0 :=
      orthogonalProjectionValuedSetFunction_disjoint_composition_zero_from_basic_laws_localization
        P (pvmSimpleFuncPairFiber f g c)
          (pvmSimpleFuncPairFiber f g d) hDisjoint x
    rw [hZero]
    simp
  · simp

/-- Canonical simple-function PVM integration is multiplicative: pointwise
multiplication of scalar multipliers becomes composition of bounded operators. -/
theorem pvmSimpleFuncSpectralIntegralOperator_mul
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f g : SimpleFunc ℝ ℝ) :
    pvmSimpleFuncSpectralIntegralOperator P (pvmSimpleFuncMul f g) =
      (pvmSimpleFuncSpectralIntegralOperator P f).comp
        (pvmSimpleFuncSpectralIntegralOperator P g) := by
  rw [pvmSimpleFuncMul]
  rw [← pvmSimpleFuncPairSpectralIntegralOperator_eq_map]
  rw [← pvmSimpleFuncPairSpectralIntegralOperator_fst_eq P f g,
    ← pvmSimpleFuncPairSpectralIntegralOperator_snd_eq P f g]
  exact
    (pvmSimpleFuncPairSpectralIntegralOperator_fst_comp_snd_eq_mul
      P f g).symm

end

end MathlibAnalytic
end MGAP4D
