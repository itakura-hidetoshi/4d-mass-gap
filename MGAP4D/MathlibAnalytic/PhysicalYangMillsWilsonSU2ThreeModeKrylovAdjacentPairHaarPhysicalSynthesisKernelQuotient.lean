import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCenteredNoUniformLowerFrame
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AD: original Wilson physical synthesis, kernel quotient and realized energy

P4-Q2-AC shows that centered adjacent Krylov coefficient vectors can
have constant coefficient-l2 norm even though their ORIGINAL posterior
innovation norms tend to zero. This does not imply that physical
Hilbert vectors have vanishing coercivity in their OWN norm.

Construct the finite REAL coefficient synthesis
  A_r : (Fin (r+1) -> ℝ) ->ₗ[ℝ] (original frozen full-link PiLp 2),
  A_r a = ∑_j a_j (I_frozen,e (S_fine^j u_H))_e.

Prove the exact original Gram identity
  a^T G_original a = ‖A_r a‖².
Its zero-energy radical is EXACTLY ker(A_r), not a substitute kernel.
Mathlib's first isomorphism theorem gives the honest independent-mode
physical realization
  coefficients / ker(A_r) ≃ₗ[ℝ] range(A_r),
with physical Rayleigh equal to the ambient physical norm squared
of the realized quotient representative.

In particular quotienting by *actual* dependencies is distinct from
assuming an inverse bound relative to the old redundant coefficient
Euclidean norm. The finite realized span also admits its canonical
orthogonal projection, which fixes all synthesized physical modes.

Neither a volume-uniform gap nor coefficient-frame invertibility,
continuum mass gap, new axiom, sorry/admit, Dobrushin or replacement
posterior/transfer is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- Linear synthesis of any FINITE family of real physical vectors.
No basis/linear independence is assumed. -/
noncomputable def p4Q2AD_realFiniteSynthesis
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun a := ∑ i : ι, a i • v i
  map_add' a b := by
    classical
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t a := by
    classical
    simp only [Pi.smul_apply, smul_sum, smul_smul]

/-- The algebraic kernel is precisely the set of finite relations. -/
theorem p4Q2AD_realFiniteSynthesis_mem_ker_iff
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) (a : ι → ℝ) :
    a ∈ (p4Q2AD_realFiniteSynthesis v).ker ↔
      (∑ i : ι, a i • v i) = 0 := by
  rw [LinearMap.mem_ker]
  rfl

/-- The realized image of a finite coefficient synthesis IS EXACTLY the
finite linear span of the original physical vectors. -/
theorem p4Q2AD_realFiniteSynthesis_range_eq_span
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) :
    (p4Q2AD_realFiniteSynthesis v).range =
      Submodule.span ℝ (Set.range v) := by
  classical
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    change (∑ i : ι, a i • v i) ∈ Submodule.span ℝ (Set.range v)
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine ⟨(fun j : ι => if j = i then (1 : ℝ) else 0), ?_⟩
    change (∑ j : ι,
      (if j = i then (1 : ℝ) else 0) • v j) = v i
    simp

/-- The first isomorphism theorem realizes the quotient by genuine
physical dependencies as the actual independent image subspace. -/
noncomputable def p4Q2AD_realFiniteSynthesis_quotientEquivRange
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) :
    ((ι → ℝ) ⧸ (p4Q2AD_realFiniteSynthesis v).ker) ≃ₗ[ℝ]
      (p4Q2AD_realFiniteSynthesis v).range :=
  (p4Q2AD_realFiniteSynthesis v).quotKerEquivRange

/-- In the physical quotient realization the representative is literally
the original synthesized vector (not the Euclidean quotient norm). -/
theorem p4Q2AD_realFiniteSynthesis_quotient_apply
    {ι : Type*} [Fintype ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) (a : ι → ℝ) :
    ((p4Q2AD_realFiniteSynthesis_quotientEquivRange v)
      (Submodule.Quotient.mk a) : E) =
      ∑ i : ι, a i • v i := by
  simpa only [p4Q2AD_realFiniteSynthesis_quotientEquivRange,
    LinearMap.quotKerEquivRange_apply_mk] using
    (LinearMap.quotKerEquivRange_apply_mk (p4Q2AD_realFiniteSynthesis v) a)

/-- The finite physical span has a canonical orthogonal projection.
Finite-dimensionality, NOT a made-up independence hypothesis, gives
completeness of the realized physical subspace. -/
noncomputable def p4Q2AD_finitePhysicalSpanProjection
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) : E →L[ℝ] E := by
  classical
  let F : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  letI : FiniteDimensional ℝ F :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  exact F.starProjection

/-- Orthogonal projection onto the physical realized finite span fixes
EVERY finite synthesized physical vector, even for dependent inputs. -/
theorem p4Q2AD_finitePhysicalSpanProjection_fixes_synthesis
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (v : ι → E) (a : ι → ℝ) :
    p4Q2AD_finitePhysicalSpanProjection v
        ((p4Q2AD_realFiniteSynthesis v) a) =
      (p4Q2AD_realFiniteSynthesis v) a := by
  classical
  let F : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hMem : (p4Q2AD_realFiniteSynthesis v) a ∈ F := by
    rw [← p4Q2AD_realFiniteSynthesis_range_eq_span v]
    exact LinearMap.mem_range_self (p4Q2AD_realFiniteSynthesis v) a
  change F.starProjection ((p4Q2AD_realFiniteSynthesis v) a) =
    (p4Q2AD_realFiniteSynthesis v) a
  exact F.starProjection_eq_self_iff.mpr hMem

local instance p4ADGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ADCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ADSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ADMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ADBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ADLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4ADComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The REAL original-Wilson, frozen-beta full-spatial-link posterior
innovation synthesis on the TRUE fine-right Krylov orbit. -/
noncomputable def fineRightKrylov_originalPhysicalFullLinkSynthesis
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    (Fin (r+1) → ℝ) →ₗ[ℝ]
      PiLp 2 (fun _ : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n+1)) =>
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent (n+1)) 2) :=
  p4Q2AD_realFiniteSynthesis
    (fun j : Fin (r+1) =>
      WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n+1)) =>
        physicalOriginalReceiverPosteriorInnovation
          (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ))))

/-- Existing exact full-link Gram identity, now expressed as the
SQUARED ambient norm of the actual physical synthesis map. -/
theorem fineRightKrylov_originalGram_rayleigh_eq_synthesis_norm_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ) :
    star a ⬝ᵥ
      Matrix.mulVec (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a =
      ‖fineRightKrylov_originalPhysicalFullLinkSynthesis
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a‖ ^ 2 := by
  exact fineRightKrylovPairHaarResidualGram_rayleigh_eq_fullLinkWeightedSum_sq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a

/-- Original posterior Gram zero-energy coefficients are EXACTLY
the kernel of the actual physical full-link synthesis; no extraneous
coefficient norm or unverified injectivity is used. -/
theorem fineRightKrylov_originalGram_zero_iff_physicalSynthesis_kernel
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ) :
    (star a ⬝ᵥ
      Matrix.mulVec (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a = 0) ↔
      a ∈ (fineRightKrylov_originalPhysicalFullLinkSynthesis
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r).ker := by
  let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hGram : (star a ⬝ᵥ
      Matrix.mulVec (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) = ‖T a‖ ^ 2 :=
    fineRightKrylov_originalGram_rayleigh_eq_synthesis_norm_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  rw [hGram, LinearMap.mem_ker]
  constructor
  · intro h
    have hz : ‖T a‖ = 0 := by
      nlinarith [norm_nonneg (T a)]
    exact norm_eq_zero.mp hz
  · intro h
    simp [h]

/-- Canonical independent physical realization: quotient of REAL
Krylov coefficients by the genuine posterior synthesis kernel is
linearly equivalent to its original all-link PiLp 2 image. -/
noncomputable def fineRightKrylov_originalPhysicalQuotientEquivRange
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    ((Fin (r+1) → ℝ) ⧸
      (fineRightKrylov_originalPhysicalFullLinkSynthesis
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r).ker) ≃ₗ[ℝ]
      (fineRightKrylov_originalPhysicalFullLinkSynthesis
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r).range :=
  (fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r).quotKerEquivRange

/-- The true Gram energy equals the norm on the PHYSICAL realized image
of the coefficient's quotient class. This is NOT an equality involving
the quotient's inherited Euclidean coefficient seminorm. -/
theorem fineRightKrylov_originalGram_eq_quotientRealization_norm_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ) :
    star a ⬝ᵥ
      Matrix.mulVec (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a =
      ‖fineRightKrylov_originalPhysicalQuotientEquivRange
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r (Submodule.Quotient.mk a)‖ ^ 2 := by
  let T := fineRightKrylov_originalPhysicalFullLinkSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hGram :=
    fineRightKrylov_originalGram_rayleigh_eq_synthesis_norm_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hQuot :
      ((T.quotKerEquivRange (Submodule.Quotient.mk a) : T.range) :
        PiLp 2 (fun _ : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n+1)) =>
          PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent (n+1)) 2)) =
      T a := by
    exact LinearMap.quotKerEquivRange_apply_mk T a
  calc
    star a ⬝ᵥ Matrix.mulVec (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) a = ‖T a‖ ^ 2 := hGram
    _ = ‖T.quotKerEquivRange (Submodule.Quotient.mk a)‖ ^ 2 := by
      rw [← hQuot]
      rfl

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
