import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonUniformQuadraticRemainderV5_JF
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# P4-Q2-JG — strong C(Cfg) and genuine Haar-L² beta-zero Wilson derivative

JF proves an UNCONDITIONAL quadratic beta Taylor error estimate
  ‖F_beta - 1 - beta D_H‖_sup ≤ (beta M_H)^2
for the entire physical compact SU(2) right-boundary configuration,
whenever ‖beta M_H‖≤1, where D_H is JE's real original Wilson
spatial-action first-variation profile.

At each fixed finite volume, beta -> ‖beta M_H‖ is continuous at 0.
The uniform bound is therefore O(beta²) = o(beta) in Banach supnorm.
The pinned mathlib HasDerivAt.of_isLittleO characterizes the
genuine STRONG derivative in C(Cfg_H,ℝ). Composing with the actual
continuous linear map C(Cfg_H,ℝ) -> Haar-L² then proves a STRONG
norm-valued derivative of the ORIGINAL Wilson Haar row in L², with
exactly JE's nonzero and nonconstant first-variation vector.

This is genuinely stronger than merely pointwise beta derivatives
or constructing an L² representative of a pointwise derivative.
It concerns the unnormalized original one-slab Haar row, which IV
identifies with the physical one-slab transfer of the Haar constant
unit at nonnegative beta. No substitute independent conditional
posterior or fake source frame is introduced.

This does NOT prove that any actual interacting two-Wilson-posterior
GI second context detects the genuine first-variation direction,
nor a finite-volume-uniform beta radius, H1-C3 or the continuum 4D
Yang–Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalStrongWilsonDerivative

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "F" =>
  p4Q2JF_originalWilsonHaarRowContinuous H
local notation "D" =>
  p4Q2JE_originalWilsonHaarZeroDerivativeProfile H

/-- The true all-right-boundary Wilson Haar row, as a function into
the Banach space C(Cfg_H,ℝ), has the ACTUAL strong beta-zero
derivative equal to the nonconstant physical spatial-action profile
D_H. The proof uses the JF uniform quadratic Taylor remainder and
no positivity assumptions on beta: this is a TWO-SIDED derivative. -/
theorem p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_supNorm :
    HasDerivAt F D 0 := by
  have hZero : F 0 = (1 : C(Cfg, ℝ)) := by
    apply ContinuousMap.ext
    intro B
    change p4Q2IV_originalWilsonUnitHaarKernelSection H 0 B = 1
    exact p4Q2IW_originalWilsonHaarRow_beta_zero H B
  have hNear : ∀ᶠ t in 𝓝 (0 : ℝ), ‖t * M‖ ≤ 1 := by
    have hContinuous : ContinuousAt (fun t : ℝ => ‖t * M‖) 0 := by
      fun_prop
    have ht : Tendsto (fun t : ℝ => ‖t * M‖) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using hContinuous.tendsto
    have hOpen : {s : ℝ | s < 1} ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds (by norm_num)
    exact (ht.eventually hOpen).mono fun t ht' => le_of_lt ht'
  have hQuadratic :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖F t - F 0 - t • D‖ ≤ M ^ 2 * ‖t ^ 2‖ := by
    filter_upwards [hNear] with t hsmall
    have hb := p4Q2JF_originalWilsonHaarRow_supNormQuadraticRemainder_le
      H t hsmall
    change ‖F t - (1 : C(Cfg, ℝ)) - t • D‖ ≤ (t * M) ^ 2 at hb
    rw [hZero]
    calc
      ‖F t - (1 : C(Cfg, ℝ)) - t • D‖ ≤ (t * M) ^ 2 := hb
      _ = M ^ 2 * ‖t ^ 2‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
        ring
  have hBig :
      (fun t : ℝ => F t - F 0 - t • D) =O[𝓝 (0 : ℝ)]
        (fun t : ℝ => t ^ 2) :=
    IsBigO.of_bound (M ^ 2) hQuadratic
  have hLittle :
      (fun t : ℝ => t ^ 2) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t) :=
    isLittleO_pow_id (by norm_num : 1 < (2 : ℕ))
  apply HasDerivAt.of_isLittleO
  simpa only [sub_zero] using hBig.trans_isLittleO hLittle

/-- The derivative can be transported by the ACTUAL bounded real-linear
embedding of continuous spatial-boundary functions into genuine
normalized physical SU(2) product-Haar L². This is a STRONG
norm-valued Haar-L² derivative of the original Wilson Haar row. -/
theorem p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_strongHaarL2 :
    HasDerivAt
      (fun beta : ℝ =>
        ContinuousMap.toLp 2 haar ℝ
          (p4Q2JF_originalWilsonHaarRowContinuous H beta))
      (p4Q2JE_originalWilsonHaarZeroDerivativeLp H) 0 := by
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar :=
    ContinuousMap.toLp 2 haar ℝ
  have hF := p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_supNorm H
  have hComp := L.hasFDerivAt.comp_hasDerivAt 0 hF
  simpa only [L, Function.comp_def,
    p4Q2JE_originalWilsonHaarZeroDerivativeLp] using hComp

/-- The strong L² beta derivative is a genuine NONZERO finite-volume
physical Haar-L² vector; it is the exact spatial Wilson action first
variation and cannot be confused with the constant-unit direction.
This does not imply the original GI conditional Wilson detector
separates this direction. -/
theorem p4Q2JG_originalWilsonHaarRow_strongHaarL2Derivative_nonzero :
    HasDerivAt
      (fun beta : ℝ =>
        ContinuousMap.toLp 2 haar ℝ
          (p4Q2JF_originalWilsonHaarRowContinuous H beta))
      (p4Q2JE_originalWilsonHaarZeroDerivativeLp H) 0 ∧
    p4Q2JE_originalWilsonHaarZeroDerivativeLp H ≠ 0 := by
  exact ⟨p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_strongHaarL2 H,
    ne_of_gt (p4Q2JE_originalWilsonHaarZeroDerivativeLp_norm_pos H)⟩

end OriginalStrongWilsonDerivative
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_supNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_strongHaarL2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JG_originalWilsonHaarRow_strongHaarL2Derivative_nonzero
