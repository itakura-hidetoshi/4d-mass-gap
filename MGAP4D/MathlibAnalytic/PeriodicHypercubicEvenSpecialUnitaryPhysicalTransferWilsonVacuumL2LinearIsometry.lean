import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonVacuumL2Transport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The vacuum law is absolutely continuous with respect to the underlying
spatial Haar law.  This is the measure-theoretic direction needed to transport
Haar-a.e. representative identities through the ground-state transform. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta ≪
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
  exact withDensity_absolutelyContinuous _ _

/-- The representative-level ground-state transform is additive in `L²`.
The only measure change used here is vacuum absolute continuity with respect to
Haar, so the result does not assume any pointwise representative formula for
the transfer operator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta (f + g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
          H N hN beta hbeta f +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
          H N hN beta hbeta g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
    H N hN beta hbeta
  have hνμ : ν ≪ μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H N hN beta hbeta
  apply Lp.ext
  have hfg : ⇑(f + g) =ᵐ[ν] f + g :=
    hνμ.ae_eq (Lp.coeFn_add f g)
  have hUfg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta (f + g)
  have hUf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta f
  have hUg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta g
  have hUadd := Lp.coeFn_add
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
      H N hN beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
      H N hN beta hbeta g)
  filter_upwards [hfg, hUfg, hUf, hUg, hUadd] with A hfgA hUfgA hUfA hUgA hUaddA
  rw [hUfgA, hUaddA]
  simp only [Pi.add_apply]
  rw [hUfA, hUgA]
  change
    (f + g) A /
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A) =
      f A /
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 A) +
        g A /
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 A)
  simp only [Pi.add_apply] at hfgA
  rw [hfgA]
  ring

/-- The ground-state transform commutes with real scalar multiplication in
vacuum `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_smul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : ℝ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta (c • f) =
      c • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta f := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
    H N hN beta hbeta
  have hνμ : ν ≪ μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H N hN beta hbeta
  apply Lp.ext
  have hcf : ⇑(c • f) =ᵐ[ν] c • f :=
    hνμ.ae_eq (Lp.coeFn_smul c f)
  have hUcf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta (c • f)
  have hUf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta f
  have hUsmul := Lp.coeFn_smul c
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
      H N hN beta hbeta f)
  filter_upwards [hcf, hUcf, hUf, hUsmul] with A hcfA hUcfA hUfA hUsmulA
  rw [hUcfA, hUsmulA]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hUfA]
  simp only [Pi.smul_apply, smul_eq_mul] at hcfA
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction,
    hcfA, mul_div_assoc]

/-- The ground-state transform preserves the `L²` norm, not only its square. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta f‖ = ‖f‖ := by
  have hsq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_norm_sq
      H N hN beta hbeta f
  nlinarith [
    norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
        H N hN beta hbeta f),
    norm_nonneg f]

/-- Canonical Hilbert-space isometry implementing the ground-state transform
`f ↦ f / Ω` from spatial Haar `L²` to the vacuum-weighted boundary `L²`.
This is the transport map used below to conjugate Wilson marginal conditional
expectations back to the physical Haar carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) where
  toFun := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2
    H N hN beta hbeta
  map_add' := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_add
    H N hN beta hbeta
  map_smul' := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_smul
    H N hN beta hbeta
  norm_map' := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_norm
    H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
