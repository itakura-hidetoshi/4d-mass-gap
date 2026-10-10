import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalOrthonormalRealization
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-AF1: physical inner products and exact finite synthesis rank-nullity

Continue the genuine original Wilson frozen posterior full-link synthesis
from AD and its independent orthonormal physical coordinates from AE.

The physical-coordinate isometry preserves all mixed inner products,
not merely squared norms. The exact first-isomorphism quotient determines
the dimension of the physically realized image, and rank-nullity counts
only genuine coefficient dependencies. These dimensions alone are NOT
an identification of the rank of the original Gram matrix; that further
matrix-level theorem is reserved for AF2.

This file introduces no new transfer or posterior law.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 850000

/-- The independent coordinates preserve the entire physical inner
product; no independence hypothesis is imposed on the input family. -/
theorem p4Q2AF_realFiniteSynthesisPhysicalCoordinates_inner_eq
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E)
    (x y : (p4Q2AD_realFiniteSynthesis v).range) :
    ⟪p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v x,
      p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v y⟫_ℝ =
      ⟪x, y⟫_ℝ :=
  (p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v).inner_map_map x y

/-- Inner products of the realized quotient representatives are the
inner products of the ORIGINAL synthesized physical vectors. -/
theorem p4Q2AF_realFiniteSynthesis_quotient_inner_eq
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) (a b : ι → ℝ) :
    ⟪p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v
        ((p4Q2AD_realFiniteSynthesis v).quotKerEquivRange
          (Submodule.Quotient.mk a)),
      p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v
        ((p4Q2AD_realFiniteSynthesis v).quotKerEquivRange
          (Submodule.Quotient.mk b))⟫_ℝ =
      ⟪(p4Q2AD_realFiniteSynthesis v) a,
        (p4Q2AD_realFiniteSynthesis v) b⟫_ℝ := by
  let T := p4Q2AD_realFiniteSynthesis v
  let Φ := p4Q2AE_realFiniteSynthesisPhysicalOrthonormalCoordinates v
  change ⟪Φ (T.quotKerEquivRange (Submodule.Quotient.mk a)),
    Φ (T.quotKerEquivRange (Submodule.Quotient.mk b))⟫_ℝ =
      ⟪T a, T b⟫_ℝ
  rw [Φ.inner_map_map]
  have ha :
      ((T.quotKerEquivRange (Submodule.Quotient.mk a) : T.range) : E) = T a :=
    LinearMap.quotKerEquivRange_apply_mk T a
  have hb :
      ((T.quotKerEquivRange (Submodule.Quotient.mk b) : T.range) : E) = T b :=
    LinearMap.quotKerEquivRange_apply_mk T b
  rw [← ha, ← hb]
  rfl

/-- Independent physical dimension is exactly the dimension of
coefficients modulo actual synthesis relations. -/
theorem p4Q2AF_realFiniteSynthesis_quotient_finrank_eq
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) :
    Module.finrank ℝ
      ((ι → ℝ) ⧸ (p4Q2AD_realFiniteSynthesis v).ker) =
      Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range :=
  (p4Q2AD_realFiniteSynthesis v).quotKerEquivRange.finrank_eq

/-- Finite synthesis rank-nullity without a linearly independent
coefficient assumption. -/
theorem p4Q2AF_realFiniteSynthesis_rankNullity
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) :
    Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range +
      Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).ker =
      Fintype.card ι := by
  calc
    _ = Module.finrank ℝ (ι → ℝ) :=
      (p4Q2AD_realFiniteSynthesis v).finrank_range_add_finrank_ker
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℝ

local instance p4AFGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AFCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AFSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AFMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AFBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AFLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AFComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Original frozen Wilson full-link synthesis has exactly (r+1)
coefficient dimensions split between genuine physical modes and relations. -/
theorem fineRightKrylov_originalPhysicalSynthesis_rankNullity
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
    Module.finrank ℝ T.range + Module.finrank ℝ T.ker = r + 1 := by
  let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  change Module.finrank ℝ T.range + Module.finrank ℝ T.ker = r + 1
  calc
    _ = Module.finrank ℝ (Fin (r + 1) → ℝ) :=
      T.finrank_range_add_finrank_ker
    _ = r + 1 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The original Wilson independent physical mode count is precisely
the dimension of the coefficient quotient by actual posterior relations. -/
theorem fineRightKrylov_originalPhysicalSynthesis_quotient_finrank_eq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
    Module.finrank ℝ ((Fin (r + 1) → ℝ) ⧸ T.ker) =
      Module.finrank ℝ T.range := by
  let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  change Module.finrank ℝ ((Fin (r + 1) → ℝ) ⧸ T.ker) =
    Module.finrank ℝ T.range
  exact T.quotKerEquivRange.finrank_eq

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
