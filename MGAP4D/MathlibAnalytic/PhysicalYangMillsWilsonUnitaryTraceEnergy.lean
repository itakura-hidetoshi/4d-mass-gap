import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProperFunctionalLimit
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

/-- The normalized real trace of a complex unitary matrix. -/
def normalizedUnitaryRealTrace
    (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) : ℝ :=
  (∑ i : Fin N, (U i i).re) / (N : ℝ)

/-- Every diagonal real part of a unitary matrix lies in `[-1,1]`. -/
theorem unitary_diagonal_re_mem_Icc
    {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (i : Fin N) :
    (U i i).re ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnorm : ‖U i i‖ ≤ 1 :=
    entry_norm_bound_of_unitary U.property i i
  have habs : |(U i i).re| ≤ 1 :=
    (RCLike.abs_re_le_norm (U i i)).trans hnorm
  exact abs_le.mp habs

/-- The normalized real trace of a positive-dimensional unitary matrix lies in
`[-1,1]`. -/
theorem normalizedUnitaryRealTrace_mem_Icc
    {N : ℕ}
    (hN : 0 < N)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    normalizedUnitaryRealTrace N U ∈ Set.Icc (-1 : ℝ) 1 := by
  have hlower :
      -(N : ℝ) ≤ ∑ i : Fin N, (U i i).re := by
    calc
      -(N : ℝ) = ∑ _i : Fin N, (-1 : ℝ) := by simp
      _ ≤ ∑ i : Fin N, (U i i).re := by
        exact Finset.sum_le_sum fun i _ => (unitary_diagonal_re_mem_Icc U i).1
  have hupper :
      (∑ i : Fin N, (U i i).re) ≤ (N : ℝ) := by
    calc
      (∑ i : Fin N, (U i i).re) ≤ ∑ _i : Fin N, (1 : ℝ) := by
        exact Finset.sum_le_sum fun i _ => (unitary_diagonal_re_mem_Icc U i).2
      _ = (N : ℝ) := by simp
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  constructor
  · change (-1 : ℝ) ≤ (∑ i : Fin N, (U i i).re) / (N : ℝ)
    rw [le_div_iff₀ hNreal]
    simpa using hlower
  · change (∑ i : Fin N, (U i i).re) / (N : ℝ) ≤ (1 : ℝ)
    rw [div_le_iff₀ hNreal]
    simpa using hupper

/-- A Wilson family whose plaquette energy is represented by the normalized
real trace of a fixed-rank complex unitary matrix representation. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonUnitaryTraceEnergyFamily
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  rank : ℕ
  rank_pos : 0 < rank
  unitaryMatrix :
    ∀ n, (E.system n).base.Gauge → Matrix.unitaryGroup (Fin rank) ℂ
  plaquetteEnergy_eq :
    ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g =
        1 - normalizedUnitaryRealTrace rank (unitaryMatrix n g)

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonUnitaryTraceEnergyFamily

/-- A unitary normalized-trace realization supplies the abstract
normalized-character Wilson-energy receipt. -/
def toWilsonNormalizedCharacterEnergyFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonUnitaryTraceEnergyFamily) :
    E.WilsonNormalizedCharacterEnergyFamily :=
  { normalizedCharacter := fun n g =>
      normalizedUnitaryRealTrace W.rank (W.unitaryMatrix n g)
    normalizedCharacter_mem_Icc := fun n g =>
      normalizedUnitaryRealTrace_mem_Icc W.rank_pos (W.unitaryMatrix n g)
    plaquetteEnergy_eq := W.plaquetteEnergy_eq }

/-- The unitary normalized-trace presentation gives the universal plaquette
energy bound `2`. -/
theorem plaquetteEnergy_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonUnitaryTraceEnergyFamily)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    (E.system n).base.plaquetteEnergy g ≤ 2 :=
  W.toWilsonNormalizedCharacterEnergyFamily.plaquetteEnergy_le_two n g

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonUnitaryTraceEnergyFamily

/-- Exact periodic geometry, a concrete unitary normalized-trace Wilson energy,
and one proper `NNReal` physical functional controlled by the reciprocal-volume
action produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicUnitaryTraceProperNNRealFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonUnitaryTraceEnergyFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicProperNNRealFunctional
    E H W.toWilsonNormalizedCharacterEnergyFamily
      functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
