import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalSynthesisKernelQuotient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# P4-Q2-AE: independent orthonormal coordinates of the original Wilson
# full-link realized posterior innovation space

After AD, the true finite original-Wilson Krylov synthesis has an exact
kernel quotient and a finite-dimensional image of ORIGINAL signed
all-spatial-link frozen posterior innovations.

Mathlib constructs a real orthonormal basis on this *physical IMAGE*
(no fictitious Gram-Schmidt pivot positivity). Its repr is a real
linear ISOMETRIC equivalence with EuclideanSpace ℝ (Fin physicalRank).

Consequently, for the original posterior Gram, one can choose a SINGLE
physical orthonormal coordinate system at each finite n,r with
  a^T G_original a =
    ‖repr (quotientRealization [a])‖_Euclidean²
for ALL real coefficient vectors a, not just the all-one or centered
ones. Rank may be less than r+1, and may change with r; no coefficient
lower-frame bound follows. Physical energy is preserved exactly, not
redefined or approximated by the redundant coefficient Euclidean norm.

No new law/operator, no Dobrushin, axiom/sorry/admit, volume-uniform or
continuum Yang--Mills mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 850000

/-- Any finite family of real physical Hilbert vectors admits a
canonical (mathlib-chosen) orthonormal basis for its TRUE realized
linear image, without assuming that the original family is independent. -/
noncomputable def p4Q2AE_realFiniteSynthesisRangeOrthonormalBasis
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range))
      ℝ (p4Q2AD_realFiniteSynthesis v).range := by
  classical
  letI : FiniteDimensional ℝ
      (p4Q2AD_realFiniteSynthesis v).range := by
    rw [p4Q2AD_realFiniteSynthesis_range_eq_span v]
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  exact stdOrthonormalBasis ℝ _

/-- Genuine orthonormal physical coordinates: these coordinates belong
to the realized independent image, not the redundant coefficient space. -/
noncomputable def p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) :
    (p4Q2AD_realFiniteSynthesis v).range ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ
        (Fin (Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range)) :=
  (p4Q2AE_realFiniteSynthesisRangeOrthonormalBasis v).repr

/-- Orthonormalization of the REALIZED image preserves the physical
Hilbert norm exactly, including the case of zero-dimensional image. -/
theorem p4Q2AE_realFiniteSynthesisPhysicalCoordinates_norm_eq
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E)
    (x : (p4Q2AD_realFiniteSynthesis v).range) :
    ‖p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v x‖ =
      ‖(x : E)‖ := by
  simpa using
    ((p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v).norm_map x)

/-- The finite synthesis quotient does not alter true physical
energy when passed to independent orthonormal realized coordinates. -/
theorem p4Q2AE_realFiniteSynthesis_quotient_physicalEnergy_preserved
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) (a : ι → ℝ) :
    ‖p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v
        ((p4Q2AD_realFiniteSynthesis v).quotKerEquivRange
          (Submodule.Quotient.mk a))‖ ^ 2 =
      ‖(p4Q2AD_realFiniteSynthesis v) a‖ ^ 2 := by
  have h := p4Q2AE_realFiniteSynthesisPhysicalCoordinates_norm_eq v
    ((p4Q2AD_realFiniteSynthesis v).quotKerEquivRange
      (Submodule.Quotient.mk a))
  have hLift :
      (((p4Q2AD_realFiniteSynthesis v).quotKerEquivRange
          (Submodule.Quotient.mk a) :
            (p4Q2AD_realFiniteSynthesis v).range) : E) =
        (p4Q2AD_realFiniteSynthesis v) a :=
    LinearMap.quotKerEquivRange_apply_mk _ _
  rw [h, hLift]

local instance p4AEGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AECompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AESecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AEMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AEBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AELinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AEComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- A SINGLE physical orthonormal basis, chosen at the true finite
Wilson volume and depth, converts EVERY original Wilson frozen
posterior Gram Rayleigh into the Euclidean squared norm of the
realized independent coordinates.

This exact isometry does not identify the norm of a redundant
coefficient a with the norm of its quotient class or its physical image. -/
theorem fineRightKrylov_originalGram_exists_orthonormalPhysicalCoordinates
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
    ∃ k : ℕ, ∃ Φ : T.range ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ a : Fin (r+1) → ℝ,
        (star a ⬝ᵥ Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r) a) =
          ‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖ ^ 2 := by
  classical
  let H := halfExtent (n+1)
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let V (j : Fin (r+1)) :=
    WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)))
  let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  let Φ := p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates V
  change ∃ k : ℕ, ∃ Ψ : T.range ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
    ∀ a : Fin (r+1) → ℝ,
      (star a ⬝ᵥ Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
        ‖Ψ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖ ^ 2
  refine ⟨Module.finrank ℝ T.range, Φ, ?_⟩
  intro a
  have hEnergy :=
    fineRightKrylov_originalGram_eq_quotientRealization_norm_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hNorm : ‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖ =
      ‖T.quotKerEquivRange (Submodule.Quotient.mk a)‖ :=
    Φ.norm_map _
  calc
    star a ⬝ᵥ Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a =
        ‖T.quotKerEquivRange (Submodule.Quotient.mk a)‖ ^ 2 := hEnergy
    _ = ‖Φ (T.quotKerEquivRange (Submodule.Quotient.mk a))‖ ^ 2 :=
      (congrArg (fun x : ℝ => x ^ 2) hNorm).symm

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
