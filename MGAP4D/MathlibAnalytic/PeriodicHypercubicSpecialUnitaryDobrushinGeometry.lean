import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonPlaquetteSupport
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure ContinuousCompactOrientedGaugeWilsonFourDimensionalIncidenceCertificate
    (C : ContinuousCompactOrientedGaugeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card C.base.geometry.Edge
  activeNeighborCard_le_eighteen :
    ∀ target : C.base.geometry.Edge,
      (C.base.activePlaquetteNeighbors target).card ≤ 18
  activeSharedPlaquetteCard_le_one :
    ∀ (target source : C.base.geometry.Edge),
      source ∈ C.base.activePlaquetteNeighbors target →
        (C.base.sharedPlaquettes target source).card ≤ 1

@[simp] theorem periodicHypercubicSpecialUnitary_touches_iff
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.PlaquetteTouchesEdge p e ↔
      periodicHypercubicPlaquetteTouchesEdge n p e := by
  rfl

theorem periodicHypercubicSpecialUnitary_activeNeighbors_eq
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.activePlaquetteNeighbors target =
      periodicHypercubicActiveNeighbors n target := by
  classical
  apply Finset.ext
  intro source
  constructor
  · intro hSource
    have hGeneric :=
      (compact_oriented_mem_activePlaquetteNeighbors_iff
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta hBeta).base target source).mp hSource
    apply (periodicHypercubic_mem_activeNeighbors_iff
      n target source).mpr
    simpa only [periodicHypercubicSpecialUnitary_touches_iff] using hGeneric
  · intro hSource
    have hConcrete :=
      (periodicHypercubic_mem_activeNeighbors_iff
        n target source).mp hSource
    apply (compact_oriented_mem_activePlaquetteNeighbors_iff
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base target source).mpr
    simpa only [periodicHypercubicSpecialUnitary_touches_iff] using hConcrete

theorem periodicHypercubicSpecialUnitary_sharedPlaquettes_eq
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.sharedPlaquettes target source =
      periodicHypercubicSharedPlaquettes n target source := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hGeneric :=
      (compact_oriented_mem_sharedPlaquettes_iff
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta hBeta).base target source p).mp hp
    apply (periodicHypercubic_mem_sharedPlaquettes_iff
      n target source p).mpr
    simpa only [periodicHypercubicSpecialUnitary_touches_iff] using hGeneric
  · intro hp
    have hConcrete :=
      (periodicHypercubic_mem_sharedPlaquettes_iff
        n target source p).mp hp
    apply (compact_oriented_mem_sharedPlaquettes_iff
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base target source p).mpr
    simpa only [periodicHypercubicSpecialUnitary_touches_iff] using hConcrete

end
end MathlibAnalytic
end MGAP4D
