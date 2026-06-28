import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonUnitaryTraceEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical determinant-forgetting inclusion `SU(N) -> U(N)`. -/
def specialUnitaryToUnitary
    (N : ℕ) :
    Matrix.specialUnitaryGroup (Fin N) ℂ →*
      Matrix.unitaryGroup (Fin N) ℂ where
  toFun U :=
    ⟨U.1, Matrix.specialUnitaryGroup_le_unitaryGroup U.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The normalized real trace of a special unitary matrix, defined through the
canonical inclusion into the unitary group. -/
def normalizedSpecialUnitaryRealTrace
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  normalizedUnitaryRealTrace N (specialUnitaryToUnitary N U)

/-- The normalized real trace of a positive-dimensional special unitary matrix
lies in `[-1,1]`. -/
theorem normalizedSpecialUnitaryRealTrace_mem_Icc
    {N : ℕ}
    (hN : 0 < N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N U ∈ Set.Icc (-1 : ℝ) 1 :=
  normalizedUnitaryRealTrace_mem_Icc hN (specialUnitaryToUnitary N U)

/-- A Wilson family whose gauge groups carry fixed-rank special-unitary
representations and whose plaquette energy is the standard normalized real-trace
Wilson energy. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryTraceEnergyFamily
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  rank : ℕ
  rank_pos : 0 < rank
  representation :
    ∀ n,
      (E.system n).base.Gauge →*
        Matrix.specialUnitaryGroup (Fin rank) ℂ
  plaquetteEnergy_eq :
    ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g =
        1 - normalizedSpecialUnitaryRealTrace rank (representation n g)

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryTraceEnergyFamily

/-- Forgetting the determinant-one condition gives the corresponding unitary
normalized-trace energy family. -/
def toWilsonUnitaryTraceEnergyFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonSpecialUnitaryTraceEnergyFamily) :
    E.WilsonUnitaryTraceEnergyFamily :=
  { rank := W.rank
    rank_pos := W.rank_pos
    unitaryMatrix := fun n g =>
      specialUnitaryToUnitary W.rank (W.representation n g)
    plaquetteEnergy_eq := by
      intro n g
      simpa [normalizedSpecialUnitaryRealTrace] using
        W.plaquetteEnergy_eq n g }

/-- A special-unitary trace realization supplies the abstract normalized
character receipt. -/
def toWilsonNormalizedCharacterEnergyFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonSpecialUnitaryTraceEnergyFamily) :
    E.WilsonNormalizedCharacterEnergyFamily :=
  W.toWilsonUnitaryTraceEnergyFamily.toWilsonNormalizedCharacterEnergyFamily

/-- Standard special-unitary Wilson plaquette energies are bounded above by two. -/
theorem plaquetteEnergy_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonSpecialUnitaryTraceEnergyFamily)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    (E.system n).base.plaquetteEnergy g ≤ 2 :=
  W.toWilsonUnitaryTraceEnergyFamily.plaquetteEnergy_le_two n g

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryTraceEnergyFamily

/-- Exact periodic geometry, an `SU(N)` normalized-trace Wilson energy, and one
proper `NNReal` physical functional controlled by the reciprocal-volume action
produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryTraceProperNNRealFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonSpecialUnitaryTraceEnergyFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicUnitaryTraceProperNNRealFunctional
    E H W.toWilsonUnitaryTraceEnergyFamily
      functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
