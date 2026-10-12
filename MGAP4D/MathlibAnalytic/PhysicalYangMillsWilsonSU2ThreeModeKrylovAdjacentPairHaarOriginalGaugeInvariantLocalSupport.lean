import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszSharpMaxColorFullL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.Tactic

/-!
# P4-Q2-ED: ACTUAL local SU(N) spatial gauge symmetry and one-link support

EA proved the best universal arbitrary nonnegative spatial-link weight coefficient
on actual six-color hypercubic link geometry. EB and EC carried that coefficient
to the original physical Wilson Haar-reference Riesz quadratic and endomorphism.
But EA's single-link weights are not automatically the squared Haar-reference
defects of physically admissible GAUGE-INVARIANT original Wilson observables.

Here we use the TRUE spatial-slice gauge action already implemented for the
genuine finite periodic SU(N) Wilson system, including the real link rule
  (gamma * A)_e = gamma(source(e)) * A_e * gamma(target(e))^-1.

The source and target of each ACTUAL spatial link are distinct because
the side length is 2*(H+1) >= 2. Thus, for any configuration A and ANY
desired link value u in SU(N), there exists a genuine vertex gauge
transformation sending A_e exactly to u. This yields a concrete physical
one-boundary gauge-invariance obstruction: a function of A_e alone that is
invariant under all local spatial gauge transformations MUST be constant.

In contrast, the actual TWO-boundary relative link variable
  R_e(A,B) = A_e^-1 * B_e
transforms by conjugation at the target vertex. Hence ANY class function
phi : SU(N) -> R gives a simultaneously gauge-invariant two-boundary
relative-link observable. Its pointwise constancy is equivalent to phi's
constancy, so no false one-link no-go for two-boundary class observables is
claimed.

All conclusions are POINTWISE about the original physical gauge
configuration carrier. They do not assume an observable realizes EA's
arbitrary spike in physical Wilson or independent pair-Haar L2, do not
identify Wilson/Haar conditional projections, do not assert nonconstant
class functions for rank N=1, do not assume color-block spectral estimates,
and do not claim uniform-in-H or continuum mass gaps. No sorry/admit/axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 850000

section ActualSpatialGauge

variable (H N : ℕ)

local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N
local notation "Act" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N

/-- A genuine spatial periodic link never closes on its own source;
side length 2*(H+1) rules out length-one periodic self-loops. -/
theorem p4Q2ED_actualSpatialLink_source_ne_target (e : Link) :
    periodicHypercubicEvenSpatialSliceShift H e.1 e.2 ≠ e.1 := by
  intro he
  have hn : 2 ≤ PeriodicHypercubicEvenSideLength H := by
    unfold PeriodicHypercubicEvenSideLength
    omega
  have hv := congrArg Subtype.val he
  have hshift :
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) e.1.1 e.2.1 =
        e.1.1 := by
    simpa only [periodicHypercubicEvenSpatialSliceShift_coe] using hv
  exact (periodicHypercubicShift_ne_self
    (PeriodicHypercubicEvenSideLength H) hn e.1.1 e.2.1) hshift

/-- ACTUAL local vertex gauge group acts transitively on the value of
any selected genuine spatial link, at any chosen background configuration.
No replacement measure or synthetic edge carrier is used. -/
theorem p4Q2ED_actualOneLinkValue_gaugeReachable
    (e : Link) (A : Cfg) (u : G) :
    ∃ γ : Gauge, (Act γ A) e = u := by
  classical
  let γ : Gauge := fun v =>
    if v = e.1 then u * (A e)⁻¹ else (1 : G)
  refine ⟨γ, ?_⟩
  have hs : γ e.1 = u * (A e)⁻¹ := by
    simp [γ]
  have ht : γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [γ, p4Q2ED_actualSpatialLink_source_ne_target H e]
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_apply, hs, ht]
  group

/-- Every POINTWISE observable depending ONLY on a single link of ONE
spatial boundary is gauge invariant under the full ACTUAL local gauge
group exactly when its underlying group function is constant. -/
theorem p4Q2ED_oneBoundary_singleLink_gaugeInvariant_iff_constant
    (e : Link) (phi : G → ℝ) :
    (∀ (γ : Gauge) (A : Cfg),
      phi ((Act γ A) e) = phi (A e)) ↔
    (∀ u v : G, phi u = phi v) := by
  constructor
  · intro hInv u v
    let A : Cfg := fun _ => v
    obtain ⟨γ, hReach⟩ :=
      p4Q2ED_actualOneLinkValue_gaugeReachable H N e A u
    have h := hInv γ A
    rw [hReach] at h
    simpa [A] using h
  · intro hConst γ A
    exact hConst _ _

/-- Even if a two-boundary observable is presented as a function of one
chosen link on just the RIGHT boundary, simultaneous original spatial
gauge invariance still forces its link function to be constant. This
does NOT apply to genuinely two-boundary relative-link observables. -/
theorem p4Q2ED_pair_oneBoundarySingleLink_gaugeInvariant_iff_constant
    (e : Link) (phi : G → ℝ) :
    (∀ (γ : Gauge) (A B : Cfg),
      phi ((Act γ B) e) = phi (B e)) ↔
    (∀ u v : G, phi u = phi v) := by
  constructor
  · intro hInv
    apply (p4Q2ED_oneBoundary_singleLink_gaugeInvariant_iff_constant
      H N e phi).mp
    intro γ B
    exact hInv γ B B
  · intro hc γ A B
    exact hc _ _

/-- The actual two-boundary relative link belongs to a conjugacy orbit,
NOT the freely transitive one-boundary gauge orbit. This is an already
established exact original one-slab gauge covariance identity. -/
theorem p4Q2ED_relativePairLink_actualGaugeCovariance
    (e : Link) (γ : Gauge) (A B : Cfg) :
    ((Act γ A) e)⁻¹ * ((Act γ B) e) =
      γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) *
        ((A e)⁻¹ * B e) *
          (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ := by
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_relative
    H N γ A B e

/-- Every conjugation-invariant real function on the genuine SU(N) group
gives a simultaneously gauge-invariant REAL two-boundary relative-link
observable on the ACTUAL original one-slab configuration carrier.
No artificial product measure or change of physical law enters. -/
theorem p4Q2ED_relativePairClassFunction_actualGaugeInvariant
    (e : Link) (phi : G → ℝ)
    (hClass : ∀ g x : G, phi (g * x * g⁻¹) = phi x) :
    ∀ (γ : Gauge) (A B : Cfg),
      phi (((Act γ A) e)⁻¹ * ((Act γ B) e)) =
        phi ((A e)⁻¹ * B e) := by
  intro γ A B
  rw [p4Q2ED_relativePairLink_actualGaugeCovariance H N e γ A B]
  exact hClass _ _

/-- Unlike one-boundary one-link observables, the two-boundary relative
observable is pointwise constant precisely when its class function
is constant. Its possible nonconstancy remains in the true pair carrier. -/
theorem p4Q2ED_relativePairObservable_constant_iff
    (e : Link) (phi : G → ℝ) :
    (∀ A B : Cfg,
      phi ((A e)⁻¹ * B e) = phi (1 : G)) ↔
    (∀ u : G, phi u = phi (1 : G)) := by
  constructor
  · intro h u
    let A : Cfg := fun _ => (1 : G)
    let B : Cfg := fun _ => u
    have hAt := h A B
    simpa [A, B] using hAt
  · intro h A B
    exact h _

/-- In particular a NONCONSTANT class function, when supplied as genuine
data, gives a gauge-invariant but nonconstant TWO-boundary local observable.
No claim of a specific nonconstant class function for every rank N. -/
theorem p4Q2ED_nonconstantRelativeClassFunction_survivesGauge
    (e : Link) (phi : G → ℝ)
    (hClass : ∀ g x : G, phi (g * x * g⁻¹) = phi x)
    (hNonconst : ∃ u v : G, phi u ≠ phi v) :
    (∀ (γ : Gauge) (A B : Cfg),
      phi (((Act γ A) e)⁻¹ * ((Act γ B) e)) =
        phi ((A e)⁻¹ * B e)) ∧
    (∃ A B C D : Cfg,
      phi ((A e)⁻¹ * B e) ≠ phi ((C e)⁻¹ * D e)) := by
  refine ⟨p4Q2ED_relativePairClassFunction_actualGaugeInvariant
    H N e phi hClass, ?_⟩
  obtain ⟨u, v, huv⟩ := hNonconst
  refine ⟨(fun _ => (1 : G)), (fun _ => u),
    (fun _ => (1 : G)), (fun _ => v), ?_⟩
  simpa using huv

end ActualSpatialGauge
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2ED_actualOneLinkValue_gaugeReachable
#print axioms MGAP4D.MathlibAnalytic.p4Q2ED_oneBoundary_singleLink_gaugeInvariant_iff_constant
#print axioms MGAP4D.MathlibAnalytic.p4Q2ED_pair_oneBoundarySingleLink_gaugeInvariant_iff_constant
#print axioms MGAP4D.MathlibAnalytic.p4Q2ED_relativePairClassFunction_actualGaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.p4Q2ED_nonconstantRelativeClassFunction_survivesGauge
