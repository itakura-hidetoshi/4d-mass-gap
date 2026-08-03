import MGAP4D.MathlibAnalytic.FiniteWilsonOSOneLayerIdentityTransfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroDiscreteOSHeatBathComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance geometricOSIdentityComparisonNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance geometricOSIdentityComparisonTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance geometricOSIdentityComparisonCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance geometricOSIdentityComparisonSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance geometricOSIdentityComparisonMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance geometricOSIdentityComparisonBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The exact defect between the canonical beta-zero boundary heat-bath step
and the geometric one-layer OS identity transfer.  The explicit isometric
bridge prevents any hidden identification of the two Hilbert carriers. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      P.OneLayerHilbert :=
  periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
    H N hN a boundaryToGeometricOS P.oneLayerIdentityTransfer

/-- Vanishing of the geometric-identity/heat-bath defect is exactly pointwise
triviality of the beta-zero one-step heat-bath operator. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff_pointwise
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
        P H N hN a boundaryToGeometricOS = 0 ↔
      ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN 0 le_rfl a f = f := by
  rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2]
  constructor
  · intro hD f
    have hIntertwine :=
      (periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2_eq_zero_iff
        H N hN a boundaryToGeometricOS P.oneLayerIdentityTransfer).mp hD
    apply boundaryToGeometricOS.injective
    simpa using (hIntertwine f).symm
  · intro hFixed
    apply
      (periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2_eq_zero_iff
        H N hN a boundaryToGeometricOS P.oneLayerIdentityTransfer).2
    intro f
    rw [P.oneLayerIdentityTransfer_apply, hFixed f]

/-- Operator form of the obstruction: the defect vanishes precisely when the
sampled beta-zero heat-bath step is the identity operator. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
        P H N hN a boundaryToGeometricOS = 0 ↔
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a = 1 := by
  rw [
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff_pointwise]
  constructor
  · intro hFixed
    apply ContinuousLinearMap.ext
    intro f
    rw [hFixed f]
    rfl
  · intro hOperator f
    have hf := ContinuousLinearMap.congr_fun hOperator f
    simpa using hf

/-- A genuinely nonidentity beta-zero heat-bath step cannot be identified with
the geometric one-layer transfer extracted from the current OS form. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_ne_zero_of_heatBath_ne_one
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a ≠ 1) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
        P H N hN a boundaryToGeometricOS ≠ 0 := by
  intro hD
  apply hHeatBath
  exact
    (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
      P H N hN a boundaryToGeometricOS).mp hD

/-- Under zero defect the entire sampled beta-zero heat-bath family is trivial,
not merely its one-step member. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_eq_one_of_geometricOSIdentityDefect_eq_zero
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (hD :
      periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
        P H N hN a boundaryToGeometricOS = 0)
    (n : ℕ) :
    periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a n = 1 := by
  rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2_eq_pow]
  rw [
    (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
      P H N hN a boundaryToGeometricOS).mp hD]
  simp

/-- Exact dichotomy for any explicit boundary-to-geometric-OS isometry: either
the beta-zero sampled step is identity, or the one-step bridge defect is
nonzero. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentity_dichotomy
    {L : FiniteLatticeWilsonSystem}
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a = 1 ∨
      periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
        P H N hN a boundaryToGeometricOS ≠ 0 := by
  classical
  by_cases hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl a = 1
  · exact Or.inl hHeatBath
  · exact Or.inr
      (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_ne_zero_of_heatBath_ne_one
        P H N hN a boundaryToGeometricOS hHeatBath)

end

end MathlibAnalytic
end MGAP4D
