import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovModalKernelSplitV5_OI
import Mathlib.Tactic

/-!
# P4-Q2-OJ — original Wilson cross-context determinant obstruction

OI decomposes every actual right-Krylov coefficient a along the true
one-row GI detector, with zero-selector u and source synthesis S(u)=U.
Here the second row is ANY original interacting-Wilson two-posterior
HF modal detector at a genuine physical link and boundary context.

The exact two-row determinant (minor)
  M_*(u) M_c(a) - M_*(a) M_c(u)
equals M_*(u) times the OTHER actual receiver applied to the
explicit OI remainder. Since OH supplies M_*(u) != 0, the minor
vanishes if and only if that other row kills the remainder.

All such genuine minors vanish if and only if HJ's original
all-link/all-context continuous detector kills this remainder.
A nonzero minor rigorously implies its HJ Gauss-law physical source
is nonzero, WITHOUT assuming such a minor actually exists.
Thus the genuine physical obstruction remains explicit rather than
being replaced by an artificial independence/rank hypothesis.

A quantitative ratio bound is also derived whenever an original
positive lower coefficient is supplied by OH's one-row half floor.
No change to original Wilson posterior, Gauss-law physical source,
Perron half-density or frozen/fine coupling. No independent Haar
posterior, Dobrushin, sorry, admit or new axioms. All-coefficient
positive-fine GI injectivity, U0, endpoint, H1-C3 and mass gap OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Exact two-row determinant of a projected vector, for any pair of
real linear detectors. No detection independence is assumed. -/
theorem p4Q2OJ_abstract_crossReceiver_minor
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : V →ₗ[ℝ] ℝ) (u a : V) (hf : f u ≠ 0) :
    f u * g (a - (f a / f u) • u) =
      f u * g a - f a * g u := by
  rw [map_sub, map_smul, smul_eq_mul]
  calc
    f u * (g a - (f a / f u) * g u) =
        f u * g a - ((f a / f u) * f u) * g u := by ring
    _ = f u * g a - f a * g u := by
      rw [div_mul_cancel₀ _ hf]

section OriginalCrossContext
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "K" => p4Q2OI_originalKrylovModalReceiverRemainder
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Original two-link/two-context signed GI determinant formed
only from HF's true physical Wilson receiver evaluations. -/
noncomputable def p4Q2OJ_originalCrossContextModalMinor
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (e' : Link) (z' : Cfg × Cfg)
    (a : Fin (r + 1) → ℝ) : ℝ :=
  M r e z (Zero r) * M r e' z' a -
    M r e z a * M r e' z' (Zero r)

/-- The OTHER true Wilson row of the explicitly projected OI
remainder equals the literal genuine two-row determinant divided
by the selected nonzero physical zero-selector response. -/
theorem p4Q2OJ_originalCrossContextRemainder_minor
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (e' : Link) (z' : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    M r e z (Zero r) * M r e' z' (K r e z a) =
      p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z e' z' a := by
  change M r e z (Zero r) *
      M r e' z' (a - (M r e z a / M r e z (Zero r)) • Zero r) =
      M r e z (Zero r) * M r e' z' a -
      M r e z a * M r e' z' (Zero r)
  exact p4Q2OJ_abstract_crossReceiver_minor
    (M r e z) (M r e' z') (Zero r) a hAnchor

/-- One further original signed Wilson physical context detects
the OI remainder precisely when its two-row minor is nonzero.
This is a criterion, NOT a claimed existence of a nonzero minor. -/
theorem p4Q2OJ_originalCrossContextRemainder_zero_iff_minor_zero
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (e' : Link) (z' : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    M r e' z' (K r e z a) = 0 ↔
      p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z e' z' a = 0 := by
  have hMinor := p4Q2OJ_originalCrossContextRemainder_minor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z e' z' hAnchor a
  constructor
  · intro hz
    rw [hz, mul_zero] at hMinor
    exact hMinor.symm
  · intro hz
    have hProduct : M r e z (Zero r) * M r e' z' (K r e z a) = 0 :=
      hMinor.trans hz
    exact (mul_eq_zero.mp hProduct).resolve_left hAnchor

/-- Complete cross-context criterion: the explicit physical
remainder is invisible to ALL genuine original GI Wilson rows
if and only if ALL its true two-row determinants vanish. -/
theorem p4Q2OJ_originalPhysicalRemainder_fullDetector_zero_iff_allMinors
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    Full r (K r e z a) = 0 ↔
      ∀ e' : Link, ∀ z' : Cfg × Cfg,
        p4Q2OJ_originalCrossContextModalMinor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e z e' z' a = 0 := by
  constructor
  · intro hAll e' z'
    have hEval := congrArg
      (fun v : Link → C(Cfg × Cfg, ℝ) => v e' z') hAll
    have hRow : M r e' z' (K r e z a) = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hEval
    exact (p4Q2OJ_originalCrossContextRemainder_zero_iff_minor_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z e' z' hAnchor a).mp hRow
  · intro hMinors
    funext e'
    apply ContinuousMap.ext
    intro z'
    change M r e' z' (K r e z a) = 0
    exact (p4Q2OJ_originalCrossContextRemainder_zero_iff_minor_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z e' z' hAnchor a).mpr (hMinors e' z')

/-- HJ's literal physical source kernel sits inside the whole
continuous GI kernel, which in turn sits inside ANY original
single-row modal kernel. The reverse inclusions are OPEN. -/
theorem p4Q2OJ_actualPhysical_full_single_kernel_inclusions
    (r : ℕ) (e : Link) (z : Cfg × Cfg) :
    (S r).ker ≤ (Full r).ker ∧
      (Full r).ker ≤ (M r e z).ker := by
  constructor
  · exact p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  · intro a ha
    have hAll : Full r a = 0 := (LinearMap.mem_ker).mp ha
    have hEval := congrArg
      (fun v : Link → C(Cfg × Cfg, ℝ) => v e z) hAll
    apply (LinearMap.mem_ker).mpr
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hEval

/-- If ANOTHER original Wilson physical context has an actual
nonzero determinant against the OI remainder, then that remainder
synthesizes a NONZERO genuine Gauss-law physical Hilbert source.
No nonzero minor or rank-two response is assumed. -/
theorem p4Q2OJ_originalCrossContextMinor_ne_implies_physicalRemainder_ne
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (e' : Link) (z' : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z e' z' a ≠ 0) :
    S r (K r e z a) ≠ 0 := by
  intro hSource
  have hSourceKer : K r e z a ∈ (S r).ker :=
    (LinearMap.mem_ker).mpr hSource
  have hFullKer : K r e z a ∈ (Full r).ker :=
    (p4Q2OJ_actualPhysical_full_single_kernel_inclusions
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z).1 hSourceKer
  have hAll : Full r (K r e z a) = 0 :=
    (LinearMap.mem_ker).mp hFullKer
  have hMinors := (p4Q2OJ_originalPhysicalRemainder_fullDetector_zero_iff_allMinors
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z hAnchor a).mp hAll
  exact hMinor (hMinors e' z')

/-- OH supplies a real selected-row square floor q. On that
actual row the coefficient t = M(a)/M(u) is quantitatively
controlled: q*t² <= M(a)². No source norm or uniform H/r floor
is assumed by this elementary consequence. -/
theorem p4Q2OJ_originalSelectedRow_projection_weighted_bound
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (q : ℝ) (hFloor : q ≤ (M r e z (Zero r)) ^ 2)
    (a : Fin (r + 1) → ℝ) :
    q * (M r e z a / M r e z (Zero r)) ^ 2 ≤
      (M r e z a) ^ 2 := by
  calc
    q * (M r e z a / M r e z (Zero r)) ^ 2 ≤
        (M r e z (Zero r)) ^ 2 *
          (M r e z a / M r e z (Zero r)) ^ 2 :=
      mul_le_mul_of_nonneg_right hFloor (sq_nonneg _)
    _ = (M r e z a) ^ 2 := by
      rw [mul_comm, div_pow,
        div_mul_cancel₀ _ (pow_ne_zero 2 hAnchor)]

end OriginalCrossContext
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_abstract_crossReceiver_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalCrossContextRemainder_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalCrossContextRemainder_zero_iff_minor_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalPhysicalRemainder_fullDetector_zero_iff_allMinors
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_actualPhysical_full_single_kernel_inclusions
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalCrossContextMinor_ne_implies_physicalRemainder_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalSelectedRow_projection_weighted_bound
