import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCrossContextPhysicalResidualMinorV5_OJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineTransferUnitEigenmodeCriterionV5_IU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIDetectorFineZeroFactorizationV5_HC
import Mathlib.Tactic

/-!
# P4-Q2-OK — actual fine Wilson eigenline obstruction at ALL finite depths

The existing genuine SU(2) right-Krylov sources are powers of the
ORIGINAL normalized FINE physical Wilson transfer on the actual
Gauss-law Haar-L² constant unit U; the frozen posterior receiver
continues to use the distinct original frozen beta(n).

For ANY nonnegative fine beta, if the genuine fine Wilson transfer
preserves the physical U eigenline with scalar c, every actual finite
right-Krylov source lies on that SAME line with literal coefficient
c^j. Consequently, ALL OJ original two-link/two-context minor values
vanish for EVERY finite depth, EVERY real Krylov coefficient, and
EVERY original interacting-Wilson posterior row.

With the genuinely proved OH nonzero original frozen receiver anchor,
the physical synthesis kernel then coincides with HJ's actual FULL
link/context GI detector kernel at EVERY depth, even when fine beta
is positive. This is physical rank-one collapse, not GI invisibility.
Conversely, a genuinely nonzero OJ minor at ANY depth proves the
fine Wilson transfer does NOT preserve the physical unit eigenline.

Unconditionally, at fine beta=0 all original cross-minors vanish
and any nonzero minor requires beta(n+1)>0. At depth zero all minors
vanish irrespective of positive fine beta. None of these statements
claims that a nonzero minor exists at positive fine beta.

Original interacting Wilson posterior pair, the FF signed receiver,
Gauss-law physical sources, true fine/frozen Wilson operators and
Perron half-density remain unchanged. No surrogate Haar posterior,
unproved rank axiom, Dobrushin, sorry or admit. U0, common endpoint,
all-positive-fine mode separation in the non-eigenline branch,
H1-C3 and continuum 4D Yang–Mills mass gap remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Any continuous real-linear endomorphism preserving the line
of u has an EXACT scalar orbit on u, at all finite powers.
The eigenline equation is not asserted for any Wilson coupling. -/
theorem p4Q2OK_abstract_CLM_eigenline_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (u : E) (c : ℝ)
    (hEigen : T u = c • u) (j : ℕ) :
    (T ^ j) u = (c ^ j) • u := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      (T ^ (j + 1)) u = T ((T ^ j) u) := by
        rw [pow_succ']
        rfl
      _ = T ((c ^ j) • u) := by rw [ih]
      _ = (c ^ j) • T u := by rw [map_smul]
      _ = (c ^ j * c) • u := by rw [hEigen, smul_smul]
      _ = (c ^ (j + 1)) • u := by rw [pow_succ]

section ActualFineWilsonEigenline
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
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "P" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "K" => p4Q2OI_originalKrylovModalReceiverRemainder
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Original actual fine right mode at ANY depth, not an artificial
mode: on the stated true normalized Wilson eigenline it equals c^j U. -/
theorem p4Q2OK_actualFineEigenline_allRightModes
    (c : ℝ) (hEigen : Fine Unit = c • Unit) (j : ℕ) :
    Right n j = (c ^ j) • Unit := by
  change (Fine ^ j) Unit = (c ^ j) • Unit
  exact p4Q2OK_abstract_CLM_eigenline_orbit Fine Unit c hEigen j

/-- Full ACTUAL HJ Gauss-law physical Krylov source collapses onto
the same true U line with its exact original fine-eigenvalue polynomial. -/
theorem p4Q2OK_actualFineEigenline_allDepth_source_eq_unitPolynomial
    (r : ℕ) (c : ℝ) (hEigen : Fine Unit = c • Unit)
    (a : Fin (r + 1) → ℝ) :
    S r a = (∑ j : Fin (r + 1), a j * c ^ (j : ℕ)) • Unit := by
  change (∑ j : Fin (r + 1), a j • Right n (j : ℕ)) =
    (∑ j : Fin (r + 1), a j * c ^ (j : ℕ)) • Unit
  calc
    (∑ j : Fin (r + 1), a j • Right n (j : ℕ)) =
        ∑ j : Fin (r + 1), (a j * c ^ (j : ℕ)) • Unit := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [p4Q2OK_actualFineEigenline_allRightModes
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n c hEigen (j : ℕ), smul_smul]
    _ = (∑ j : Fin (r + 1), a j * c ^ (j : ℕ)) • Unit := by
      rw [Finset.sum_smul]

/-- Equal ACTUAL Gauss-law Hilbert physical sources have exactly
equal HF two-interacting-posterior signed GI values at every context.
This is the original HJ source-to-detector compatibility. -/
theorem p4Q2OK_actualEqualPhysicalSources_sameOriginalGI
    (r : ℕ) (e : Link) (z : Pair)
    (a b : Fin (r + 1) → ℝ)
    (hSource : S r a = S r b) :
    M r e z a = M r e z b := by
  have hZero : S r (a - b) = 0 := by
    rw [map_sub, hSource, sub_self]
  have hKer : a - b ∈ (P r).ker :=
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) ((LinearMap.mem_ker).mpr hZero)
  have hFull : P r (a - b) = 0 := (LinearMap.mem_ker).mp hKer
  have hAt := congrArg (fun f : Link → C(Pair, ℝ) => f e z) hFull
  have hModal : M r e z (a - b) = 0 := by
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hAt
  have hDiff : M r e z a - M r e z b = 0 := by
    simpa only [map_sub] using hModal
  exact sub_eq_zero.mp hDiff

/-- TRUE original HF signed GI row on the whole finite fine-right
Krylov family factors through the SAME scalar eigenvalue polynomial.
No genuine source-independent row rank is assumed. -/
theorem p4Q2OK_actualFineEigenline_modal_eq_unitPolynomial
    (r : ℕ) (c : ℝ) (hEigen : Fine Unit = c • Unit)
    (a : Fin (r + 1) → ℝ) (e : Link) (z : Pair) :
    M r e z a =
      (∑ j : Fin (r + 1), a j * c ^ (j : ℕ)) * M r e z (Zero r) := by
  let t : ℝ := ∑ j : Fin (r + 1), a j * c ^ (j : ℕ)
  have hPhysical : S r a = t • Unit :=
    p4Q2OK_actualFineEigenline_allDepth_source_eq_unitPolynomial
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r c hEigen a
  have hZeroUnit : S r (Zero r) = Unit := by
    change (∑ j : Fin (r + 1),
      Zero r j • Right n (j : ℕ)) = Unit
    exact p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  have hOther : S r (t • Zero r) = t • Unit := by
    rw [map_smul, hZeroUnit]
  have hRow : M r e z a = M r e z (t • Zero r) :=
    p4Q2OK_actualEqualPhysicalSources_sameOriginalGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z a (t • Zero r) (hPhysical.trans hOther.symm)
  calc
    M r e z a = M r e z (t • Zero r) := hRow
    _ = t * M r e z (Zero r) := by rw [map_smul, smul_eq_mul]

/-- Every actual OJ two-context signed Wilson minor vanishes when the
original normalized fine Wilson transfer preserves the physical U
eigenline. Valid for ALL finite r and ANY real coefficient. -/
theorem p4Q2OK_actualFineEigenline_allDepth_allWilsonMinors_zero
    (r : ℕ) (c : ℝ) (hEigen : Fine Unit = c • Unit)
    (e e' : Link) (z z' : Pair) (a : Fin (r + 1) → ℝ) :
    p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a = 0 := by
  unfold p4Q2OJ_originalCrossContextModalMinor
  rw [p4Q2OK_actualFineEigenline_modal_eq_unitPolynomial
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r c hEigen a e z,
    p4Q2OK_actualFineEigenline_modal_eq_unitPolynomial
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r c hEigen a e' z']
  ring

/-- Genuine nonzero cross-context minor at ANY depth would force
the original positive-fine normalized Wilson transfer to move U out
of its own physical eigenline. This is a NECESSARY condition and
does NOT assert any such nonzero minor exists. -/
theorem p4Q2OK_nonzeroOriginalCrossMinor_forces_fineUnit_nonEigenline
    (r : ℕ) (e e' : Link) (z z' : Pair) (a : Fin (r + 1) → ℝ)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a ≠ 0) :
    ¬ ∃ c : ℝ, Fine Unit = c • Unit := by
  rintro ⟨c, hc⟩
  exact hMinor (p4Q2OK_actualFineEigenline_allDepth_allWilsonMinors_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r c hc e e' z z' a)

/-- With a proved OH nonzero actual original Wilson signed anchor,
the explicit OI remainder is a ZERO physical Gauss-law source
through every fine eigenline Krylov depth, even if fine beta>0. -/
theorem p4Q2OK_actualFineEigenline_allDepth_remainderSource_zero
    (r : ℕ) (c : ℝ) (hEigen : Fine Unit = c • Unit)
    (e : Link) (z : Pair)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    S r (K r e z a) = 0 := by
  let k : Fin (r + 1) → ℝ := K r e z a
  let t : ℝ := ∑ j : Fin (r + 1), k j * c ^ (j : ℕ)
  have hReceiver : M r e z k = 0 :=
    p4Q2OI_originalKrylovModalRemainder_GI_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z hAnchor a
  have hScalar : t = 0 := by
    have hModal : M r e z k = t * M r e z (Zero r) :=
      p4Q2OK_actualFineEigenline_modal_eq_unitPolynomial
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r c hEigen k e z
    have hProduct : t * M r e z (Zero r) = 0 :=
      hModal.symm.trans hReceiver
    exact (mul_eq_zero.mp hProduct).resolve_right hAnchor
  have hPhysical : S r k = t • Unit :=
    p4Q2OK_actualFineEigenline_allDepth_source_eq_unitPolynomial
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r c hEigen k
  simpa only [hScalar, zero_smul] using hPhysical

/-- Same genuine fine physical eigenline: complete-original-GI
and actual physical source kernels COINCIDE at every finite depth,
provided an ACTUAL original Wilson row detects the physical U.
The kernel equality is physical rank collapse, not artificial
injectivity or nonzero high-mode detection. -/
theorem p4Q2OK_actualFineEigenline_allDepth_sourceKernel_eq_fullGIKernel
    (r : ℕ) (c : ℝ) (hEigen : Fine Unit = c • Unit)
    (e : Link) (z : Pair)
    (hAnchor : M r e z (Zero r) ≠ 0) :
    (S r).ker = (P r).ker := by
  apply le_antisymm
  · exact p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  · intro a hGlobal
    have hP : P r a = 0 := (LinearMap.mem_ker).mp hGlobal
    have hAt := congrArg (fun f : Link → C(Pair, ℝ) => f e z) hP
    have hRow : M r e z a = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAt
    let t : ℝ := ∑ j : Fin (r + 1), a j * c ^ (j : ℕ)
    have hModal : M r e z a = t * M r e z (Zero r) :=
      p4Q2OK_actualFineEigenline_modal_eq_unitPolynomial
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r c hEigen a e z
    have hProduct : t * M r e z (Zero r) = 0 :=
      hModal.symm.trans hRow
    have ht : t = 0 :=
      (mul_eq_zero.mp hProduct).resolve_right hAnchor
    apply (LinearMap.mem_ker).mpr
    have hSource : S r a = t • Unit :=
      p4Q2OK_actualFineEigenline_allDepth_source_eq_unitPolynomial
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r c hEigen a
    simpa only [ht, zero_smul] using hSource

/-- Genuine OH fixed-scale selected physical Wilson row produces
the SAME real physical synthesis/GI whole-context KERNEL EQUALITY
for ALL depths, in the specifically identified fine eigenline branch.
Frozen coupling is positive; fine coupling can be positive as well. -/
theorem p4Q2OK_actualFineEigenline_sameScale_allDepth_sourceGI_separation
    (hFrozen : 0 < beta n)
    (c : ℝ) (hEigen : Fine Unit = c • Unit)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∀ r : ℕ, (S r).ker = (P r).ker := by
  obtain ⟨z, z', hRows⟩ :=
    p4Q2OH_originalOneRow_exists_allDepth_sameContext_kernelFinrank
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  rcases hRows with hLeft | hRight
  · intro r
    exact p4Q2OK_actualFineEigenline_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r c hEigen e z (hLeft r).1
  · intro r
    exact p4Q2OK_actualFineEigenline_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r c hEigen e' z' (hRight r).1

/-- At actual FINE beta(n+1)=0, existing HC original-Wilson
two-posterior expectation response is literal rank-one in all
right-Krylov coefficients. No positive frozen beta is needed. -/
theorem p4Q2OK_fineZero_actualOriginalModal_rankOne
    (r : ℕ) (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (e : Link) (z : Pair) :
    M r e z a = (∑ j : Fin (r + 1), a j) * M r e z (Zero r) := by
  calc
    M r e z a =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • Right n (j : ℕ)) e z :=
          (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a e z).symm
    _ = (∑ j : Fin (r + 1), a j) *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (Right n 0) e z :=
            p4Q2HC_fineZero_originalGIExpectationGap_eq_sum_mul
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r hFineZero a e z
    _ = (∑ j : Fin (r + 1), a j) * M r e z (Zero r) := by
      rw [p4Q2OH_actualModal_zeroSelector_eq_originalZeroPhysicalGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z]

/-- Unconditional ACTUAL fine-beta-zero obstruction: all genuine
two-interacting-Wilson posterior cross-context minors vanish, even at
positive frozen coupling and arbitrarily high finite depth. -/
theorem p4Q2OK_fineZero_allActualWilsonCrossMinors_zero
    (r : ℕ) (hFineZero : beta (n + 1) = 0)
    (e e' : Link) (z z' : Pair) (a : Fin (r + 1) → ℝ) :
    p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a = 0 := by
  unfold p4Q2OJ_originalCrossContextModalMinor
  rw [p4Q2OK_fineZero_actualOriginalModal_rankOne
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a e z,
    p4Q2OK_fineZero_actualOriginalModal_rankOne
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a e' z']
  ring

/-- A genuinely nonzero original Wilson modal minor requires
STRICTLY POSITIVE fine coupling, not merely a positive frozen beta.
The positivity follows from the given original nonnegative schedule,
without a newly assumed analytic source frame. -/
theorem p4Q2OK_nonzeroOriginalCrossMinor_requires_positiveFine
    (r : ℕ) (e e' : Link) (z z' : Pair) (a : Fin (r + 1) → ℝ)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a ≠ 0) :
    0 < beta (n + 1) := by
  rcases lt_or_eq_of_le (hbeta (n + 1)) with hPos | hZero
  · exact hPos
  · exact False.elim (hMinor
      (p4Q2OK_fineZero_allActualWilsonCrossMinors_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hZero.symm e e' z z' a))

/-- The coefficient space of depth zero is one-dimensional.
Consequently NO genuine second original Wilson row can produce
a nonzero higher-mode minor, at ANY frozen/fine coupling. -/
theorem p4Q2OK_depthZero_allActualWilsonCrossMinors_zero
    (e e' : Link) (z z' : Pair) (a : Fin (0 + 1) → ℝ) :
    p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 e e' z z' a = 0 := by
  have hCoeff : a = a 0 • Zero 0 := by
    funext j
    fin_cases j
    simp [p4Q2GX_rightZeroCoefficient, Pi.smul_apply]
  unfold p4Q2OJ_originalCrossContextModalMinor
  rw [hCoeff]
  simp only [map_smul, smul_eq_mul]
  ring

/-- Any nonzero genuine cross-context Wilson minor needs a
NONZERO Krylov depth and positive fine Wilson coupling. A physical
eigenline failure is separately necessary by the earlier OK theorem.
These are necessary gates, not a constructed witness. -/
theorem p4Q2OK_nonzeroOriginalCrossMinor_requires_depth_and_positiveFine
    (r : ℕ) (e e' : Link) (z z' : Pair) (a : Fin (r + 1) → ℝ)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a ≠ 0) :
    0 < r ∧ 0 < beta (n + 1) := by
  have hr : 0 < r := by
    by_contra hNot
    have hz : r = 0 := Nat.eq_zero_of_not_pos hNot
    subst r
    exact hMinor (p4Q2OK_depthZero_allActualWilsonCrossMinors_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' a)
  exact ⟨hr, p4Q2OK_nonzeroOriginalCrossMinor_requires_positiveFine
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e e' z z' a hMinor⟩

end ActualFineWilsonEigenline
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_abstract_CLM_eigenline_orbit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_allRightModes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_allDepth_source_eq_unitPolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualEqualPhysicalSources_sameOriginalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_modal_eq_unitPolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_allDepth_allWilsonMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_nonzeroOriginalCrossMinor_forces_fineUnit_nonEigenline
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_allDepth_remainderSource_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_allDepth_sourceKernel_eq_fullGIKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_actualFineEigenline_sameScale_allDepth_sourceGI_separation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_fineZero_actualOriginalModal_rankOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_fineZero_allActualWilsonCrossMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_nonzeroOriginalCrossMinor_requires_positiveFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_depthZero_allActualWilsonCrossMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OK_nonzeroOriginalCrossMinor_requires_depth_and_positiveFine
