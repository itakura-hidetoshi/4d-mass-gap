import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPrimaryPlaquetteHaarModeProjectiveCylinder
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance primaryPlaquetteWilsonPowerTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryPlaquetteWilsonPowerCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryPlaquetteWilsonPowerSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryPlaquetteWilsonPowerMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryPlaquetteWilsonPowerBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The degree-`k` Wilson-energy class function on one `SU(N)` holonomy.

These powers are the concrete polynomial class-function family that will be
orthonormalized in the next layer. -/
def specialUnitaryWilsonPlaquetteEnergyPower
    (N k : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  specialUnitaryWilsonPlaquetteEnergy N U ^ k

/-- Every Wilson-energy power is invariant under conjugation. -/
theorem specialUnitaryWilsonPlaquetteEnergyPower_conjInvariant
    {N k : ℕ}
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergyPower N k (h * g * h⁻¹) =
      specialUnitaryWilsonPlaquetteEnergyPower N k g := by
  unfold specialUnitaryWilsonPlaquetteEnergyPower
  rw [specialUnitaryWilsonPlaquetteEnergy_conjInvariant]

/-- Positive-rank Wilson-energy powers have the uniform pointwise bound
`|E_W(U)^k| ≤ 2^k`. -/
theorem specialUnitaryWilsonPlaquetteEnergyPower_norm_le
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖specialUnitaryWilsonPlaquetteEnergyPower N k U‖ ≤ (2 : ℝ) ^ k := by
  have h0 := specialUnitaryWilsonPlaquetteEnergy_nonneg hN U
  have h2 := specialUnitaryWilsonPlaquetteEnergy_le_two hN U
  unfold specialUnitaryWilsonPlaquetteEnergyPower
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)]
  exact pow_le_pow_left₀ h0 h2 k

/-- Each Wilson-energy power belongs to real `L²` of normalized Haar on
`SU(N)`.  This uses only continuity, the exact bound `0 ≤ E_W ≤ 2`, and
finiteness of the normalized Haar probability measure. -/
theorem specialUnitaryWilsonPlaquetteEnergyPower_memLp
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ) :
    MemLp
      (specialUnitaryWilsonPlaquetteEnergyPower N k)
      2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  letI : IsFiniteMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    inferInstance
  exact MemLp.of_bound
    ((continuous_specialUnitaryWilsonPlaquetteEnergy N).pow k).aestronglyMeasurable
    ((2 : ℝ) ^ k)
    (Filter.Eventually.of_forall fun U =>
      specialUnitaryWilsonPlaquetteEnergyPower_norm_le hN k U)

/-- The degree-`k` Wilson-energy power as an actual normalized-Haar real `L²`
vector. -/
noncomputable def specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N := by
  change Lp ℝ 2
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  exact (specialUnitaryWilsonPlaquetteEnergyPower_memLp hN k).toLp
    (specialUnitaryWilsonPlaquetteEnergyPower N k)

/-- The normalized-Haar `L²` vector has the intended pointwise representative
almost everywhere. -/
theorem specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_coeFn
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hN k =ᵐ[
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)]
      specialUnitaryWilsonPlaquetteEnergyPower N k :=
  MemLp.coeFn_toLp
    (specialUnitaryWilsonPlaquetteEnergyPower_memLp hN k)

/-- The actual canonical primary spatial plaquette and the cyclic boundary Haar
representative have exactly the same degree-`k` Wilson-energy class function. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyPower_eq_boundaryCyclicHolonomy
    (H : ℕ)
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergyPower N k
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergyPower N k
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)) := by
  unfold specialUnitaryWilsonPlaquetteEnergyPower
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergy_eq_boundaryCyclicHolonomy]

/-- The concrete degree-`k` Wilson-energy mode realized in the full actual
boundary Haar `L²`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyPowerBoundaryHaarL2
    (H : ℕ)
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H N
    (specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hN k)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- The concrete degree-`k` Wilson-energy class function, carried through the
exact canonical-primary-plaquette Haar isometry and the existing projective
boundary readout at scale `n`. -/
noncomputable def primarySpatialPlaquetteWilsonEnergyPowerProjectiveL2Mode
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n k : ℕ) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
    (specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hN k)

/-- The projective mode is exactly the image of the concrete full-boundary Haar
mode under the density-corrected boundary/projective isometry. -/
theorem primarySpatialPlaquetteWilsonEnergyPowerProjectiveL2Mode_eq_boundary
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n k : ℕ) :
    R.primarySpatialPlaquetteWilsonEnergyPowerProjectiveL2Mode n k =
      R.boundaryHaarProjectiveL2Isometry n
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyPowerBoundaryHaarL2
          (halfExtent n) hN k) := by
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

end

end MathlibAnalytic
end MGAP4D
