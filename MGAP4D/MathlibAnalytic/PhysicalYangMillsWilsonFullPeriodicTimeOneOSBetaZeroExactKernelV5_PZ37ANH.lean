import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTwoModeOSGramBetaZeroV5_PZ37ANG0
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeOneFiniteCylinderHaarV5_PZ37AMX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANH — sharp beta-zero pointwise Wilson OS moment kernel

ANG0 proved that the original full-periodic Wilson boundary Gram moment of
the UNCHANGED time-one two-mode observable at beta zero is the original
open-half Haar mean times the original positive partition normalization.
This leaf proves the reverse direction of its ZERO locus using the ACTUAL
finite Wilson partition function positivity, without any extra assumption.

It also separates H=0 from H>0 before attempting open-half time-one
independence: for H=0, time one is exactly the antipodal fixed slice, whereas
for H>0 it is strictly interior. Therefore the Haar-fiber mean is not
asserted zero by a blanket boundary-independence argument.

No unconditional OS-nullity of the original physical top-orthogonal
coefficient pair, and no strict OS norm at beta>0, is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANH_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANH_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANH_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANH_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANH_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANH_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- Original finite Wilson partition normalization makes the scalar
beta-zero Gram kernel strictly positive, not merely nonnegative. -/
theorem p4Q2PZ37ANH_originalWilsonBetaZeroGramScalar_pos
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)] :
    0 < Real.sqrt
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
        0 (by norm_num)).base.partitionFunction⁻¹) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
    0 (by norm_num)
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  exact Real.sqrt_pos.2 (inv_pos.mpr hZ)

/-- Exact necessary AND sufficient zero criterion, pointwise in the
reflection-fixed boundary, for the same original physical two-mode time-one
Wilson cylinder.  No nonzero ordinary Gibbs/Haar L2 is used. -/
theorem p4Q2PZ37ANH_originalTimeOneBoundaryGramMoment_zero_iff_openHaarMean_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
      H 0 (by norm_num) c0 c1 b = 0 ↔
      (∫ x, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
        H c0 c1 (b, x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) = 0 := by
  rw [p4Q2PZ37ANG0_originalTimeOneBoundaryMoment_eq_openHaarMean]
  have hpos := p4Q2PZ37ANH_originalWilsonBetaZeroGramScalar_pos H
  have hne : Real.sqrt
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
        0 (by norm_num)).base.partitionFunction⁻¹) ≠ 0 :=
    ne_of_gt hpos
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hscalar | hmean
    · exact (hne hscalar).elim
    · exact hmean
  · intro h
    simp [h]

/-- Exact almost-everywhere kernel identity: at zero coupling, the original
Wilson boundary moment vanishes boundary-a.e. IFF the unchanged time-one
cylinder has zero open-half Haar fiber mean boundary-a.e. -/
theorem p4Q2PZ37ANH_originalTimeOneBoundaryMoment_ae_zero_iff_openHaarMean_ae_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ) :
    (∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
      p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H 0 (by norm_num) c0 c1 b = 0) ↔
    (∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
      (∫ x, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
        H c0 c1 (b, x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) = 0) := by
  constructor
  · intro h
    filter_upwards [h] with b hb
    exact (p4Q2PZ37ANH_originalTimeOneBoundaryGramMoment_zero_iff_openHaarMean_zero
      H c0 c1 b).mp hb
  · intro h
    filter_upwards [h] with b hb
    exact (p4Q2PZ37ANH_originalTimeOneBoundaryGramMoment_zero_iff_openHaarMean_zero
      H c0 c1 b).mpr hb

/-- At H=0, time one is the OTHER reflection-fixed boundary spatial slice.
It is not a strict open-half interior slice. -/
theorem p4Q2PZ37ANH_timeOne_zero_eq_antipodalFixed :
    p4Q2PZ37AMX_positiveTimeOne 0 =
      Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount 0) := by
  apply Fin.ext
  simp [p4Q2PZ37AMX_positiveTimeOne,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- For H>0 time one is strictly inside the positive spatial interior:
its index is below the antipodal reflection-fixed slice H+1. -/
theorem p4Q2PZ37ANH_timeOne_strictInterior_of_pos
    (H : ℕ) (hH : 0 < H) :
    (p4Q2PZ37AMX_positiveTimeOne H).val < H + 1 := by
  change 1 < H + 1
  omega

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANH_originalWilsonBetaZeroGramScalar_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANH_originalTimeOneBoundaryGramMoment_zero_iff_openHaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANH_originalTimeOneBoundaryMoment_ae_zero_iff_openHaarMean_ae_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANH_timeOne_zero_eq_antipodalFixed
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANH_timeOne_strictInterior_of_pos
