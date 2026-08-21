import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalTemporalStep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointPhysicalLinkSeparation
import Mathlib.Tactic

/-!
# Plaquette-local path separation of physical-link supports

The preceding layer defines the actual one-step Wilson locality relation on
physical positive links: two links are local when they occur in one periodic
coordinate plaquette.  Here we package finite paths of exactly `d` such local
steps and define a support-separation predicate saying that no path shorter
than `D` connects the two finite supports.

This avoids assigning a numerical infimum before the path geometry is in
place.  It is already an actual local support-distance lower-bound statement:
`D` means every plaquette-local connecting path has at least `D` steps.

As the first receipt, ordinary finite-set disjointness implies separation by
one step.  Thus the fixed-slot reflected-left / translated-right disjointness
from the midpoint geometry immediately becomes a genuine plaquette-local
path-separation statement of level one.

No decay estimate or small-coupling condition is introduced here, and no
positive mass or Hamiltonian gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A path of exactly `d` Wilson-plaquette-local steps from `e` to `f`.
The carrier has `d+1` physical links; consecutive entries are related by the
actual same-plaquette locality relation. -/
def periodicHypercubicEvenPlaquetteLocalPath
    (H d : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) : Prop :=
  ∃ γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
    γ 0 = e ∧
      γ (Fin.last d) = f ∧
        ∀ i : Fin d,
          periodicHypercubicEvenPlaquetteLocal H
            (γ i.castSucc) (γ i.succ)

/-- A zero-step local path has identical endpoints. -/
theorem periodicHypercubicEvenPlaquetteLocalPath_zero_iff
    (H : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenPlaquetteLocalPath H 0 e f ↔ e = f := by
  constructor
  · rintro ⟨γ, h0, hlast, _⟩
    have hindex : (Fin.last 0 : Fin 1) = 0 := by rfl
    calc
      e = γ 0 := h0.symm
      _ = γ (Fin.last 0) := congrArg γ hindex.symm
      _ = f := hlast
  · intro hef
    subst f
    refine ⟨fun _ => e, rfl, rfl, ?_⟩
    intro i
    exact Fin.elim0 i

/-- One actual plaquette-local step gives a path of length one. -/
theorem periodicHypercubicEvenPlaquetteLocalPath_one
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hlocal : periodicHypercubicEvenPlaquetteLocal H e f) :
    periodicHypercubicEvenPlaquetteLocalPath H 1 e f := by
  let γ : Fin 2 → PeriodicHypercubicEvenEdge H :=
    fun i => Fin.cases e (fun _ => f) i
  refine ⟨γ, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro i
    fin_cases i
    simpa [γ] using hlocal

/-- Every step of a plaquette-local path satisfies the one-unit periodic
source-time relation proved for actual Wilson plaquettes. -/
theorem periodicHypercubicEvenPlaquetteLocalPath_temporalUnitRelated
    (H d : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hpath : periodicHypercubicEvenPlaquetteLocalPath H d e f) :
    ∃ γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
      γ 0 = e ∧
        γ (Fin.last d) = f ∧
          ∀ i : Fin d,
            periodicHypercubicEvenTemporalUnitRelated H
              (γ i.castSucc) (γ i.succ) := by
  rcases hpath with ⟨γ, h0, hlast, hstep⟩
  refine ⟨γ, h0, hlast, ?_⟩
  intro i
  exact periodicHypercubicEvenPlaquetteLocal_temporalUnitRelated H (hstep i)

/-- `D` is a lower bound on the actual plaquette-local path separation of two
finite physical-link supports when no path of length `< D` connects them. -/
def periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy
    (H D : ℕ)
    (S T : Finset (PeriodicHypercubicEvenEdge H)) : Prop :=
  ∀ d : ℕ, d < D →
    ∀ e : PeriodicHypercubicEvenEdge H, e ∈ S →
      ∀ f : PeriodicHypercubicEvenEdge H, f ∈ T →
        ¬ periodicHypercubicEvenPlaquetteLocalPath H d e f

/-- A local-separation lower bound can always be weakened. -/
theorem periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_mono
    (H D D' : ℕ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hDD : D' ≤ D) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D' S T := by
  intro d hd e he f hf
  exact hsep d (lt_of_lt_of_le hd hDD) e he f hf

/-- Disjoint finite supports are separated by at least one plaquette-local
step: a path of length zero would identify its two endpoints. -/
theorem periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_one_of_disjoint
    (H : ℕ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hdisj : Disjoint S T) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H 1 S T := by
  intro d hd e he f hf hpath
  have hd0 : d = 0 := by omega
  subst d
  have hef :=
    (periodicHypercubicEvenPlaquetteLocalPath_zero_iff H e f).mp hpath
  subst f
  exact (Finset.disjoint_left.mp hdisj) he hf

/-- The fixed-slot midpoint supports already constructed in the physical
Wilson configuration are separated by at least one actual plaquette-local
step under the same hypotheses that gave their finite-set disjointness. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_plaquetteLocalSeparatedBy_one
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightPos : ∀ q : ℚ, q ∈ J →
      1 ≤ Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n))
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H 1
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r) := by
  apply periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_one_of_disjoint
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_disjoint_rightSupport
      H latticeSpacing n J r hleftWithin hrightPos hrightWithin

end

end MathlibAnalytic
end MGAP4D
