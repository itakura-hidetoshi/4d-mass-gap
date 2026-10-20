import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalActiveGIPhysicalGapAverageV5_MD
import Mathlib.Tactic

/-!
# P4-Q2-ME — genuinely full spatial Wilson physical-source gap energy

MD proves that MB's genuinely energy-active subset of the original
SU(2) Wilson spatial plaquette carrier has nonzero finite-H mean
physical two-posterior gap-square energy. Here we lift that theorem
to the FULL ORIGINAL spatial plaquette carrier.

The exact original Gauss-law physical source attached to each
plaquette p remains unchanged: x U + y W_{H,p} U. The two signed
posterior expectation gaps are evaluated at the same true
interacting-Wilson boundary contexts e,e',z,z' for every plaquette.

The complement of the active set contributes a sum of genuine
nonnegative gap squares, hence the entire spatial average bounds
MD's active-plaquette average from above. The resulting coefficient
is the square of the genuine original GI energy density Q/N times
a positive b-dependent contrast factor, with no new independent
distribution, artificial detector, substitute source or hypothesis.

In particular LY supplies ONE pair of authentic Wilson contexts
which works simultaneously for EVERY real physical-source
coefficient pair (x,y). This is a finite-H assertion: it does not
yield a positive volume-uniform infimum of Q/N, H1-C3, a continuum
Yang-Mills construction, or a positive mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2ME_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2ME_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2ME_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2ME_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2ME_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "A" => p4Q2MB_originalActiveGISpatialPlaquettes H b hb
local notation "R" =>
  p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare H b hb

/-- Genuine physical signed-posterior-gap squares are nonnegative on
every plaquette of the original spatial Wilson lattice. -/
theorem p4Q2ME_originalPhysicalPlaquetteGapSquare_nonneg
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) (x y : ℝ) :
    0 ≤ R e e' z z' p x y := by
  unfold p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare
  positivity

/-- For the same true interacting-Wilson contexts, the full spatial
carrier's physical-source gap-square sum dominates the sum over the
actual MB-filtered active plaquettes. No probabilistic substitution. -/
theorem p4Q2ME_originalFullPhysicalGapSum_ge_active
    (e e' : Link) (z z' : Cfg × Cfg) (x y : ℝ) :
    (∑ p ∈ A e e' z z', R e e' z z' p x y) ≤
      (∑ p : Plaq, R e e' z z' p x y) := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg
    (fun p : Plaq =>
      p4Q2ME_originalPhysicalPlaquetteGapSquare_nonneg
        H b hb e e' z z' p x y)

/-- The WHOLE original spatial Wilson plaquette family has actual
Gauss-law physical two-source gap-square mean at least MD's explicit
positive finite-H energy-density-square floor. -/
theorem p4Q2ME_originalFullPhysicalGapAverage_ge_energyDensitySquare
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (x y : ℝ) :
    ((Q e e' z z' / n) / (2 * (4 * E^2)^2)) *
      ((Q e e' z z' / (2 * n)) / (10 * E^2)) *
        (x^2 + y^2) ≤
      (∑ p : Plaq, R e e' z z' p x y) / n := by
  have hActive :=
    p4Q2MD_originalActivePhysicalGapAverage_ge_energyDensitySquare
      H b hb hpos hcount e e' z z' hQ x y
  have hFull :=
    p4Q2ME_originalFullPhysicalGapSum_ge_active
      H b hb e e' z z' x y
  exact hActive.trans
    ((div_le_div_iff_of_pos_right hcount).2 hFull)

/-- Every nonzero real physical source coefficient pair produces
strictly positive genuine FULL-spatial average of the two original
interacting-Wilson signed posterior gap squares, at fixed finite H
whenever the authentic original GI square energy is positive. -/
theorem p4Q2ME_originalFullPhysicalGapAverage_pos
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (x y : ℝ)
    (hSource : 0 < x^2 + y^2) :
    0 < (∑ p : Plaq, R e e' z z' p x y) / n := by
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hMean : 0 < Q e e' z z' / n := div_pos hQ hcount
  have hHalf : 0 < Q e e' z z' / (2 * n) :=
    div_pos hQ (mul_pos (by norm_num) hcount)
  have hFirstDen : 0 < 2 * (4 * E^2)^2 := by positivity
  have hSecondDen : 0 < 10 * E^2 := by positivity
  have hFloorPos :
      0 < ((Q e e' z z' / n) / (2 * (4 * E^2)^2)) *
        ((Q e e' z z' / (2 * n)) / (10 * E^2)) *
          (x^2 + y^2) :=
    mul_pos (mul_pos (div_pos hMean hFirstDen)
      (div_pos hHalf hSecondDen)) hSource
  exact lt_of_lt_of_le hFloorPos
    (p4Q2ME_originalFullPhysicalGapAverage_ge_energyDensitySquare
      H b hb hpos hcount e e' z z' hQ x y)

/-- At the authentic LY original interacting-Wilson witness contexts
ONE strictly positive physical source-plane coefficient controls the
full original spatial sum SIMULTANEOUSLY for ALL real x,y. It may
depend on finite H and the original witness contexts: there is no
asserted H-uniform positive lower bound. -/
theorem p4Q2ME_originalPhysicalGI_exists_fullSpatialTwoSourceFloor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧ 0 < Q e e' z z' / n ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ x y : ℝ,
          c * (x^2 + y^2) ≤
            (∑ p : Plaq, R e e' z z' p x y) / n := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hMean : 0 < Q e e' z z' / n := div_pos hQ hn
  have hHalf : 0 < Q e e' z z' / (2 * n) :=
    div_pos hQ (mul_pos (by norm_num) hn)
  have hFirstDen : 0 < 2 * (4 * E^2)^2 := by positivity
  have hSecondDen : 0 < 10 * E^2 := by positivity
  have hC :
      0 < ((Q e e' z z' / n) / (2 * (4 * E^2)^2)) *
        ((Q e e' z z' / (2 * n)) / (10 * E^2)) :=
    mul_pos (div_pos hMean hFirstDen) (div_pos hHalf hSecondDen)
  refine ⟨z, z', hn, hMean, _, hC, ?_⟩
  intro x y
  exact p4Q2ME_originalFullPhysicalGapAverage_ge_energyDensitySquare
    H b hb hpos hn e e' z z' hQ x y

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ME_originalPhysicalPlaquetteGapSquare_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ME_originalFullPhysicalGapSum_ge_active
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ME_originalFullPhysicalGapAverage_ge_energyDensitySquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ME_originalFullPhysicalGapAverage_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ME_originalPhysicalGI_exists_fullSpatialTwoSourceFloor
