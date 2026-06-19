import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonActionControl

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The canonical signed periodic `SU(N)` Wilson system with positivity of the
side length supplied as an ordinary theorem rather than a typeclass argument. -/
def periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
    (sideLength N : ℕ)
    (sideLength_pos : 0 < sideLength)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem := by
  letI : NeZero sideLength := ⟨Nat.ne_of_gt sideLength_pos⟩
  exact periodicHypercubicSpecialUnitaryWilsonSystem
    sideLength N hN beta beta_nonneg

/-- Exact plaquette count for the positive-side constructor. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide_plaquette_card
    (sideLength N : ℕ)
    (sideLength_pos : 0 < sideLength)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    Fintype.card
        (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
          sideLength N sideLength_pos hN beta beta_nonneg).base.geometry.Plaquette =
      6 * sideLength ^ 4 := by
  letI : NeZero sideLength := ⟨Nat.ne_of_gt sideLength_pos⟩
  change Fintype.card (PeriodicHypercubicPlaquette sideLength) =
    6 * sideLength ^ 4
  exact periodicHypercubicPlaquette_card sideLength

/-- Exact signed Wilson-action formula for the positive-side constructor. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide_wilsonAction
    (sideLength N : ℕ)
    (sideLength_pos : 0 < sideLength)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEdge sideLength →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
        sideLength N sideLength_pos hN beta beta_nonneg).base.wilsonAction A =
      ∑ p : PeriodicHypercubicPlaquette sideLength,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p) := by
  letI : NeZero sideLength := ⟨Nat.ne_of_gt sideLength_pos⟩
  exact periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction
    sideLength N hN beta beta_nonneg A

/-- Build the orientation-correct physical lattice embedding directly from a
sequence of positive periodic side lengths, fixed `SU(N)` rank, Wilson couplings,
and interpolation maps into one Polish carrier. -/
noncomputable def periodicHypercubicSpecialUnitaryPhysicalEmbedding
    {PhysicalConfiguration : Type}
    [TopologicalSpace PhysicalConfiguration]
    [MeasurableSpace PhysicalConfiguration]
    [BorelSpace PhysicalConfiguration]
    [PolishSpace PhysicalConfiguration]
    (sideLength : ℕ → ℕ)
    (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n)
    (interpolate :
      ∀ n,
        (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
          (sideLength n) N (sideLength_pos n) hN
          (beta n) (beta_nonneg n)).base.Configuration →
          PhysicalConfiguration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop) :
    ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding :=
  { PhysicalConfiguration := PhysicalConfiguration
    system := fun n =>
      periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
        (sideLength n) N (sideLength_pos n) hN
        (beta n) (beta_nonneg n)
    interpolate := interpolate
    interpolate_measurable := interpolate_measurable
    latticeSpacing := latticeSpacing
    latticeSpacing_pos := latticeSpacing_pos
    latticeSpacing_tendsto_zero := latticeSpacing_tendsto_zero
    physicalVolume := physicalVolume
    physicalVolume_tendsto_atTop := physicalVolume_tendsto_atTop }

end

end MathlibAnalytic
end MGAP4D
