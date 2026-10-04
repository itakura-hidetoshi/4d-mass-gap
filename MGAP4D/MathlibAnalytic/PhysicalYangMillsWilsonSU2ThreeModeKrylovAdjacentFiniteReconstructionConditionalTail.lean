import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionCommonProjection
import Mathlib.Tactic

/-!
# Physical-valued conditional reconstruction tail for adjacent SU(2) geometry

PR #5126 identifies the correct projection-comparison direction for the
#5124 common-marginal reconstruction variance:

  V_{n,r,k}
    = ||Y_{n,r,k} - P_n^phys Y_{n,r,k}||^2.

To upper-bound this variance by a conditional residual, the comparison output
must lie in the coarse embedded completed physical pair carrier.  A raw local
conditional expectation need not have this property, so this file does not
silently identify the two notions.

Instead it isolates the exact model-facing object needed by the receiver: a
bounded common-marginal reconstruction map whose value on each actual frozen
Krylov vector lies in the coarse embedded physical range, together with a
growing-distance tail for its squared residual.

Once such a physical-valued conditional reconstruction is produced from the
finite Wilson locality / conditional-expectation machinery, #5126 turns its
residual tail into the total reconstruction variance tail.  The existing #5123
receiver then generates geometric decay of both projective residuals.

No whole-space cross-volume compatibility, H1-D5 condition, rank-one forcing,
or exact descent of a raw local conditional expectation is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentConditionalTailTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentConditionalTailCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentConditionalTailSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentConditionalTailMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentConditionalTailBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentConditionalTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentConditionalTailSpatialHaarSFinite (H : ℕ) :
    SFinite
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentConditionalTailNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance su2AdjacentConditionalTailPairCarrierComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

section ConditionalTail

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)

/-- Model-facing conditional-reconstruction input for the #5124 common
projection variance.

The reconstruction map itself is intentionally weaker than a globally defined
conditional-expectation structure: for the present fixed-Krylov receiver it is
enough that its value on each actual frozen vector belongs to the coarse
embedded physical range.  A later Wilson theorem may instantiate it by a
genuine conditional expectation followed by a theorem-generated physical
reconstruction, provided the same range statement is proved rather than
assumed by exact descent. -/
structure PhysicalYangMillsSU2AdjacentCommonPhysicalConditionalTailInput where
  reconstruction :
    (n : ℕ) →
      Lp ℝ 2
          (F.finiteMarginal
            (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
              (Q := Q) R n)) →L[ℝ]
        Lp ℝ 2
          (F.finiteMarginal
            (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
              (Q := Q) R n))
  reconstruction_frozen_mem :
    ∀ (n r : ℕ) (k : Fin 3),
      reconstruction n
          (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
            Q R n r k) ∈
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
            (halfExtent n) 2).map
          (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding
            Q R n).toLinearMap
  reconstructionResidual_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (C rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ C ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        ∀ n,
          ‖physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
                Q R n r k -
              reconstruction n
                (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
                  Q R n r k)‖ ^ 2 ≤
            C * (rho ^ distance n / (1 - rho))

namespace PhysicalYangMillsSU2AdjacentCommonPhysicalConditionalTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentCommonPhysicalConditionalTailInput
        (Q := Q) (R := R))

include G

/-- A growing-distance tail for one physical-valued conditional reconstruction
is already a valid #5123 total reconstruction variance tail. -/
theorem totalVariance_tail
    (r : ℕ) (k : Fin 3) :
    ∃ (C rho : ℝ) (distance : ℕ → ℕ),
      0 ≤ C ∧
      0 ≤ rho ∧
      rho < 1 ∧
      (∀ n, n ≤ distance n) ∧
      ∀ n,
        physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
            Q R n r k ≤
          C * (rho ^ distance n / (1 - rho)) := by
  rcases G.reconstructionResidual_tail r k with
    ⟨C, rho, distance, hC, hrho0, hrho1, hDistance, hTail⟩
  refine ⟨C, rho, distance, hC, hrho0, hrho1, hDistance, ?_⟩
  intro n
  exact
    (physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect_le_commonCondExpResidual_sq_of_mem
      Q R n r k (G.reconstruction n)
      (G.reconstruction_frozen_mem n r k)).trans
      (hTail n)

/-- Package a physical-valued conditional reconstruction tail together with the
two independent geometric lanes into the #5123 variance-geometric receiver. -/
noncomputable def toFiniteReconstructionVarianceGeometricInput
    (physicalCommutation_geometric :
      ∀ (r : ℕ) (k : Fin 3),
        ∃ C q : ℝ,
          0 ≤ q ∧ q < 1 ∧
            ∀ n : ℕ,
              physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                  Q R n r k ≤
                C * q ^ n)
    (betaMajorant_geometric :
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentCouplingBetaMajorant
                halfExtent beta n ≤
              C * q ^ n) :
    PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput
      (Q := Q) (R := R) where
  physicalCommutation_geometric := physicalCommutation_geometric
  totalVariance_tail := totalVariance_tail Q R G
  betaMajorant_geometric := betaMajorant_geometric

/-- Final receiver: a physical-valued conditional reconstruction tail, finite
physical transfer/reconstruction commutation decay, and the explicit beta
majorant imply summability of every fixed Krylov-orbit mismatch. -/
theorem orbitMismatch_summable
    (physicalCommutation_geometric :
      ∀ (r : ℕ) (k : Fin 3),
        ∃ C q : ℝ,
          0 ≤ q ∧ q < 1 ∧
            ∀ n : ℕ,
              physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                  Q R n r k ≤
                C * q ^ n)
    (betaMajorant_geometric :
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentCouplingBetaMajorant
                halfExtent beta n ≤
              C * q ^ n)
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput.orbitMismatch_summable
      Q R
      (toFiniteReconstructionVarianceGeometricInput
        Q R G physicalCommutation_geometric betaMajorant_geometric)
      r k

end PhysicalYangMillsSU2AdjacentCommonPhysicalConditionalTailInput


/-- Obstruction-aware model-facing input after #5128.

A raw bounded common-marginal candidate is allowed without any assertion that
its range is physical.  For each fixed Krylov depth and mode, the raw
conditional residual and the physicality defect are required to share one
growing-distance geometric envelope.  Their constants may differ.

The shared `rho` and `distance` are only an envelope convention; a later
model theorem may always enlarge two compatible tails to a common envelope.
-/
structure PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput where
  candidate :
    (n : ℕ) →
      Lp ℝ 2
          (F.finiteMarginal
            (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
              (Q := Q) R n)) →L[ℝ]
        Lp ℝ 2
          (F.finiteMarginal
            (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
              (Q := Q) R n))
  splitResidual_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (Craw Cphys rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ Craw ∧
        0 ≤ Cphys ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        (∀ n,
          ‖physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
                Q R n r k -
              candidate n
                (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
                  Q R n r k)‖ ^ 2 ≤
            Craw * (rho ^ distance n / (1 - rho))) ∧
        ∀ n,
          ‖candidate n
                (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
                  Q R n r k) -
              physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
                Q R n
                (candidate n
                  (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
                    Q R n r k))‖ ^ 2 ≤
            Cphys * (rho ^ distance n / (1 - rho))

namespace PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput
        (Q := Q) (R := R))

include G

/-- The two #5128 obstruction terms with one shared growing-distance envelope
generate the single total reconstruction variance tail required by #5123.

The resulting constant is exactly `2*Craw + 2*Cphys`. -/
theorem totalVariance_tail
    (r : ℕ) (k : Fin 3) :
    ∃ (C rho : ℝ) (distance : ℕ → ℕ),
      0 ≤ C ∧
      0 ≤ rho ∧
      rho < 1 ∧
      (∀ n, n ≤ distance n) ∧
      ∀ n,
        physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
            Q R n r k ≤
          C * (rho ^ distance n / (1 - rho)) := by
  rcases G.splitResidual_tail r k with
    ⟨Craw, Cphys, rho, distance,
      hCraw, hCphys, hrho0, hrho1, hDistance, hRaw, hPhys⟩
  refine
    ⟨2 * Craw + 2 * Cphys, rho, distance,
      add_nonneg (mul_nonneg (by norm_num) hCraw)
        (mul_nonneg (by norm_num) hCphys),
      hrho0, hrho1, hDistance, ?_⟩
  intro n
  let Y :=
    physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
      Q R n r k
  let Cn := G.candidate n
  let P :=
    physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
      Q R n
  let tail := rho ^ distance n / (1 - rho)
  have hSplit :
      physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
          Q R n r k ≤
        2 * ‖Y - Cn Y‖ ^ 2 +
          2 * ‖Cn Y - P (Cn Y)‖ ^ 2 := by
    simpa [Y, Cn, P] using
      physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect_le_two_commonCondExpResidual_sq_add_two_physicalityResidual_sq
        Q R n r k Cn
  have hRawN : ‖Y - Cn Y‖ ^ 2 ≤ Craw * tail := by
    simpa [Y, Cn, tail] using hRaw n
  have hPhysN : ‖Cn Y - P (Cn Y)‖ ^ 2 ≤ Cphys * tail := by
    simpa [Y, Cn, P, tail] using hPhys n
  have hRaw2 :
      2 * ‖Y - Cn Y‖ ^ 2 ≤ 2 * (Craw * tail) :=
    mul_le_mul_of_nonneg_left hRawN (by norm_num)
  have hPhys2 :
      2 * ‖Cn Y - P (Cn Y)‖ ^ 2 ≤ 2 * (Cphys * tail) :=
    mul_le_mul_of_nonneg_left hPhysN (by norm_num)
  calc
    physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
        Q R n r k ≤
      2 * ‖Y - Cn Y‖ ^ 2 +
        2 * ‖Cn Y - P (Cn Y)‖ ^ 2 := hSplit
    _ ≤ 2 * (Craw * tail) + 2 * (Cphys * tail) :=
      add_le_add hRaw2 hPhys2
    _ = (2 * Craw + 2 * Cphys) *
        (rho ^ distance n / (1 - rho)) := by
      dsimp [tail]
      ring

/-- Package the obstruction-aware conditional split together with the two
independent geometric lanes into the #5123 variance-geometric receiver. -/
noncomputable def toFiniteReconstructionVarianceGeometricInput
    (physicalCommutation_geometric :
      ∀ (r : ℕ) (k : Fin 3),
        ∃ C q : ℝ,
          0 ≤ q ∧ q < 1 ∧
            ∀ n : ℕ,
              physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                  Q R n r k ≤
                C * q ^ n)
    (betaMajorant_geometric :
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentCouplingBetaMajorant
                halfExtent beta n ≤
              C * q ^ n) :
    PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput
      (Q := Q) (R := R) where
  physicalCommutation_geometric := physicalCommutation_geometric
  totalVariance_tail := totalVariance_tail Q R G
  betaMajorant_geometric := betaMajorant_geometric

/-- Final obstruction-aware receiver: separate tails for the raw common
conditional residual and its physicality defect, plus the finite
transfer/reconstruction commutation and beta lanes, imply summability of every
fixed Krylov-orbit mismatch. -/
theorem orbitMismatch_summable
    (physicalCommutation_geometric :
      ∀ (r : ℕ) (k : Fin 3),
        ∃ C q : ℝ,
          0 ≤ q ∧ q < 1 ∧
            ∀ n : ℕ,
              physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                  Q R n r k ≤
                C * q ^ n)
    (betaMajorant_geometric :
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentCouplingBetaMajorant
                halfExtent beta n ≤
              C * q ^ n)
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput.orbitMismatch_summable
      Q R
      (toFiniteReconstructionVarianceGeometricInput
        Q R G physicalCommutation_geometric betaMajorant_geometric)
      r k

end PhysicalYangMillsSU2AdjacentCommonConditionalPhysicalityTailInput


end ConditionalTail

end

end MathlibAnalytic
end MGAP4D
