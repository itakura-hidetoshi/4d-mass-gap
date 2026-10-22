import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoExactGIKernelV5_OP
import Mathlib.Tactic

/-!
# P4-Q2-OQ — authentic Wilson quadratic physical orbit collapse and all-depth GI/source equality

OO #5806 builds the ACTUAL right-Krylov depth-two Gauss-law Schur source
from U, normalized physical fine Wilson T_t U and T_t^2 U. OP #5807
proves its exact GI/source kernel obstruction using two actual
interacting frozen-Wilson posterior receiver contexts.

Here we use the ORIGINAL normalized physical Wilson continuous linear
operator. A zero genuine depth-two Schur physical source, under OM's
PROVED nonzero leading two-context minor, yields an actual quadratic
Wilson orbit relation T_t^2 U = alpha U + gamma T_t U. Unlike a
surrogate rank hypothesis, this relation is DERIVED from the true
physical source identity and the specific explicit Schur coefficient.

By applying the actual Wilson transfer recursively we prove EVERY
true right-Krylov power and EVERY finite-depth source synthesizes
in the SAME U, T_t U plane. The TWO authentic interacting posterior
GI contexts, already proved separating on that physical plane by
OM/ON, then imply for every depth r:

  ker S_r = ker Phi_all,r

Thus, on the true quadratic-collapse branch, there is NO physically
nonzero globally GI-invisible source at ANY finite Krylov depth.

Finally, an UNCONDITIONAL finite-volume small-positive-fine dichotomy
is proved: either this SAME all-depth physical/GI kernel equality
holds or the actual depth-two Schur PHYSICAL HILBERT SOURCE is nonzero.
The second branch is an authentic physical nonzero witness, NOT
a proved third genuine GI receiver detection. The separate third-row
and uniform/H-limit/continuum obstructions remain OPEN.

All physical laws, FF signed receiver, two genuine interacting Wilson
posteriors, Gauss law, normalized fine/frozen coupling distinction and
Perron half-density remain unchanged. No Dobrushin, independent Haar,
new rank premise, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The actual two-dimensional cyclic plane is preserved by a linear
transfer satisfying a genuine quadratic equation ON THE PHYSICAL UNIT.
This is an elementary operator-theoretic deduction, not a hypothesis
of GI rank or third-source independence. -/
theorem p4Q2OQ_abstract_quadraticCLM_allPowers_twoMode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (u : E) (alpha gamma : ℝ)
    (hQuadratic : (T ^ 2) u = alpha • u + gamma • T u)
    (j : ℕ) :
    ∃ x y : ℝ, (T ^ j) u = x • u + y • T u := by
  induction j with
  | zero =>
    refine ⟨1, 0, ?_⟩
    simp
  | succ j ih =>
    obtain ⟨x, y, hxy⟩ := ih
    have hTwo : T (T u) = alpha • u + gamma • T u := by
      calc
        T (T u) = (T ^ 2) u := by
          rw [pow_succ']
          rfl
        _ = alpha • u + gamma • T u := hQuadratic
    refine ⟨y * alpha, x + y * gamma, ?_⟩
    calc
      (T ^ (j + 1)) u = T ((T ^ j) u) := by
        rw [pow_succ']
        rfl
      _ = T (x • u + y • T u) := by rw [hxy]
      _ = x • T u + y • (alpha • u + gamma • T u) := by
        rw [map_add, map_smul, map_smul, hTwo]
      _ = (y * alpha) • u + (x + y * gamma) • T u := by
        rw [smul_add, smul_smul, smul_smul, add_smul]
        abel

/-- For an ACTUAL physical cyclic triple, vanishing of a signed
Schur source with NONZERO leading scalar determinant supplies an
explicit quadratic transfer relation. The argument solves a vector
equation by the already-proved nonzero real scalar only. -/
theorem p4Q2OQ_abstract_nonzeroSchurScalar_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (u : E)
    (delta A B : ℝ) (hDelta : delta ≠ 0)
    (hSchur : delta • (T ^ 2) u - A • u - B • T u = 0) :
    ∃ alpha gamma : ℝ,
      (T ^ 2) u = alpha • u + gamma • T u := by
  have hScaled : delta • (T ^ 2) u = A • u + B • T u := by
    apply sub_eq_zero.mp
    calc
      delta • (T ^ 2) u - (A • u + B • T u) =
          delta • (T ^ 2) u - A • u - B • T u := by abel
      _ = 0 := hSchur
  refine ⟨delta⁻¹ * A, delta⁻¹ * B, ?_⟩
  calc
    (T ^ 2) u = (1 : ℝ) • (T ^ 2) u := by simp
    _ = (delta⁻¹ * delta) • (T ^ 2) u := by rw [inv_mul_cancel₀ hDelta]
    _ = delta⁻¹ • (delta • (T ^ 2) u) := by rw [smul_smul]
    _ = delta⁻¹ • (A • u + B • T u) := by rw [hScaled]
    _ = (delta⁻¹ * A) • u + (delta⁻¹ * B) • T u := by
      rw [smul_add, smul_smul, smul_smul]

section ActualWilsonQuadraticCollapse
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Right" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "First" => p4Q2IS_depthOneCoefficient
local notation "Second" => p4Q2OO_depthTwoSecondCoefficient

/-- Original normalized fine physical Wilson transfer has a genuine
quadratic U orbit IF its exact OO depth-two Schur physical source
vanishes at two ORIGINAL interacting-posterior GI contexts with
OM's PROVED nonzero first-two minor. No rank premise is added. -/
theorem p4Q2OQ_actualSchurPhysicalZero_implies_quadraticWilsonUnit
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor
      (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0) :
    ∃ alpha gamma : ℝ,
      (Fine ^ 2) Unit = alpha • Unit + gamma • Fine Unit := by
  let delta : ℝ := p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z')
  let A : ℝ :=
    M 2 e z Second * M 2 e' z' p4Q2OO_depthTwoFirstCoefficient -
      M 2 e z p4Q2OO_depthTwoFirstCoefficient * M 2 e' z' Second
  let B : ℝ :=
    M 2 e z (Zero 2) * M 2 e' z' Second -
      M 2 e z Second * M 2 e' z' (Zero 2)
  have hPhys :=
    p4Q2OO_actualDepthTwo_SchurResidual_physicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z'
  change S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) =
    delta • ((Fine ^ 2) Unit) - A • Unit - B • (Fine Unit) at hPhys
  have hEq :
      delta • ((Fine ^ 2) Unit) - A • Unit - B • (Fine Unit) = 0 :=
    hPhys.symm.trans hSchur
  exact p4Q2OQ_abstract_nonzeroSchurScalar_quadratic Fine Unit
    delta A B hMinor hEq

/-- The ACTUAL unchanged Wilson normalized fine transfer is
quadratically cyclic on the true Gauss-law physical unit in the
Schur-vanishing branch: EVERY finite right-Krylov power is in the
literal REAL span of U and T_fine U. -/
theorem p4Q2OQ_actualSchurPhysicalZero_allRightModes_twoMode
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor
      (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0)
    (j : ℕ) :
    ∃ x y : ℝ,
      Right n j = x • Unit + y • Fine Unit := by
  obtain ⟨alpha, gamma, hQuadratic⟩ :=
    p4Q2OQ_actualSchurPhysicalZero_implies_quadraticWilsonUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor hSchur
  change ∃ x y : ℝ, (Fine ^ j) Unit = x • Unit + y • Fine Unit
  exact p4Q2OQ_abstract_quadraticCLM_allPowers_twoMode
    Fine Unit alpha gamma hQuadratic j

/-- This is the actual HJ physical Hilbert source for ARBITRARY finite
right-Krylov depth and ALL real coefficients, not an artificially
truncated source or just the first three formal modes. -/
theorem p4Q2OQ_actualSchurPhysicalZero_allDepth_source_twoMode
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor
      (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0)
    (r : ℕ) (a : Fin (r + 1) → ℝ) :
    ∃ x y : ℝ, S r a = x • Unit + y • Fine Unit := by
  classical
  have hEach (j : Fin (r + 1)) :
      ∃ x y : ℝ,
        Right n (j : ℕ) = x • Unit + y • Fine Unit :=
    p4Q2OQ_actualSchurPhysicalZero_allRightModes_twoMode
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor hSchur (j : ℕ)
  choose x y hxy using hEach
  refine ⟨∑ j : Fin (r + 1), a j * x j,
          ∑ j : Fin (r + 1), a j * y j, ?_⟩
  change (∑ j : Fin (r + 1), a j • Right n (j : ℕ)) =
    (∑ j : Fin (r + 1), a j * x j) • Unit +
      (∑ j : Fin (r + 1), a j * y j) • Fine Unit
  calc
    (∑ j : Fin (r + 1), a j • Right n (j : ℕ)) =
        ∑ j : Fin (r + 1),
          ((a j * x j) • Unit + (a j * y j) • Fine Unit) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hxy j, smul_add, smul_smul, smul_smul]
    _ = (∑ j : Fin (r + 1), a j * x j) • Unit +
          (∑ j : Fin (r + 1), a j * y j) • Fine Unit := by
      rw [Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_smul]

/-- The TRUE frozen two-interacting-posterior GI pair already proved
separating at depth one by OM/ON detects EVERY physical right-Krylov
source whenever the REAL normalized fine Wilson orbit actually
closes quadratically on U. At ALL finite depths, physical source
and ENTIRE continuous original GI detector have IDENTICAL kernels.

This does not postulate (or prove) that the original fine Wilson
operator always has a quadratic cyclic orbit at positive fine. -/
theorem p4Q2OQ_actualSchurPhysicalZero_allDepth_sourceKernel_eq_fullGIKernel
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor
      (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0)
    (r : ℕ) :
    (S r).ker = (Full r).ker := by
  apply le_antisymm
  · exact p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  · intro a ha
    have hFull : Full r a = 0 := (LinearMap.mem_ker).mp ha
    obtain ⟨x, y, hSource⟩ :=
      p4Q2OQ_actualSchurPhysicalZero_allDepth_source_twoMode
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e e' z z' hMinor hSchur r a
    let b : Fin (1 + 1) → ℝ := x • Zero 1 + y • First
    have hBasis :=
      p4Q2OM_actualDepthOne_zeroFirst_physicalSources
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
    have hB : S 1 b = x • Unit + y • Fine Unit := by
      change S 1 (x • Zero 1 + y • First) =
        x • Unit + y • Fine Unit
      rw [map_add, map_smul, map_smul, hBasis.1, hBasis.2]
    have hEqualSource : S r a = S 1 b :=
      hSource.trans hB.symm
    have hMinor1 : p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 1 e e' z z' First ≠ 0 := by
      rw [← p4Q2OO_actualDepthTwo_leadingMinor_eq_originalDepthOneMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e e' z z']
      exact hMinor
    have hAt0 := congrArg (fun f : Link → C(Pair, ℝ) => f e z) hFull
    have hAt1 := congrArg (fun f : Link → C(Pair, ℝ) => f e' z') hFull
    have hRow0 : M r e z a = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAt0
    have hRow1 : M r e' z' a = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAt1
    have hTransport (link : Link) (context : Pair) :
        M r link context a = M 1 link context b := by
      have hr :=
        p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a link context
      have hb :=
        p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 1 b link context
      change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (S r a) link context =
          M r link context a at hr
      change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (S 1 b) link context =
          M 1 link context b at hb
      rw [hEqualSource] at hr
      exact hr.symm.trans hb
    have hb0 : M 1 e z b = 0 := by
      rw [← hTransport e z]
      exact hRow0
    have hb1 : M 1 e' z' b = 0 := by
      rw [← hTransport e' z']
      exact hRow1
    have hbCoeff : b = 0 :=
      p4Q2ON_twoActualWilsonRows_commonKernel_eq_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e e' z z' hMinor1 b hb0 hb1
    apply (LinearMap.mem_ker).mpr
    rw [hEqualSource, hbCoeff, map_zero]

/-- An UNCONDITIONAL actual SU(2) Wilson small-positive-fine,
finite-volume, positive-frozen-coupling theorem:
one genuine pair of GI contexts and ONE finite positive-fine window
exhibit the exact dichotomy, valid at EVERY finite right-Krylov depth.

Either the ORIGINAL Gauss-law physical source synthesis and its
ENTIRE original interacting-posterior GI detector have the same
kernel for ALL r, or the explicitly constructed SAME genuine
depth-two Schur source has a NONZERO PHYSICAL HILBERT IMAGE.

The second alternative does not force a genuine third GI response.
U0, arbitrary positive fine, endpoint, strong limit and 4d
Yang-Mills mass gap remain OPEN. -/
theorem p4Q2OQ_actualSmallFine_allDepthGIKernelEquality_or_depthTwoPhysicalObstruction
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Pair, ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (∀ r : ℕ, (S r).ker = (Full r).ker) ∨
          S 2 (p4Q2OO_depthTwoSchurResidual
            (M 2 e z) (M 2 e' z')) ≠ 0) := by
  obtain ⟨z, z', delta, hDelta, hFine⟩ :=
    p4Q2OO_actualDepthTwo_exists_nonzeroLeadingMinor_smallFine
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', delta, hDelta, ?_⟩
  intro ht hsmall
  have hMinor := hFine ht hsmall
  by_cases hPhysical : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0
  · left
    intro r
    exact p4Q2OQ_actualSchurPhysicalZero_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor hPhysical r
  · exact Or.inr hPhysical

end ActualWilsonQuadraticCollapse
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_abstract_quadraticCLM_allPowers_twoMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_abstract_nonzeroSchurScalar_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_actualSchurPhysicalZero_implies_quadraticWilsonUnit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_actualSchurPhysicalZero_allRightModes_twoMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_actualSchurPhysicalZero_allDepth_source_twoMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_actualSchurPhysicalZero_allDepth_sourceKernel_eq_fullGIKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OQ_actualSmallFine_allDepthGIKernelEquality_or_depthTwoPhysicalObstruction
