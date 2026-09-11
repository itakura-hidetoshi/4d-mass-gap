import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TopEigenspaceBlockDynamics
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance topEigenspaceBlockOrthogonalityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance topEigenspaceBlockOrthogonalityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance topEigenspaceBlockOrthogonalitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance topEigenspaceBlockOrthogonalityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance topEigenspaceBlockOrthogonalityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance topEigenspaceBlockOrthogonalitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance topEigenspaceBlockOrthogonalitySpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A decomposable vector in the full top-top block `F ⊠ F`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta u)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta v)

/-- A decomposable vector in the left-excitation/right-top block `K ⊠ F`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta u)

/-- A decomposable vector in the left-top/right-excitation block `F ⊠ K`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta u)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta f)

/-- A decomposable vector in the double-excitation block `K ⊠ K`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta g)

private theorem periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f) = 0 := by
  have hf := f.property
  change
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ at hf
  rw [Submodule.mem_orthogonal] at hf
  have hphysical :
      inner ℝ
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
          (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) = 0 :=
    hf
      (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
      u.property
  change
    inner ℝ
        (((u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
        (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) = 0
  exact hphysical

private theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_inner_topEigenspace_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u) = 0 := by
  rw [real_inner_comm]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero
      H N hN beta hbeta u f

/-- `F ⊠ F` is orthogonal to `K ⊠ F` on decomposable vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTop_inner_orthogonalTop_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v w : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
          H N hN beta hbeta u v)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
          H N hN beta hbeta f w) = 0 := by
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta v))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta w)) = 0
  rw [realL2ExternalTensor_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero,
    zero_mul]

/-- `F ⊠ F` is orthogonal to `F ⊠ K` on decomposable vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTop_inner_topOrthogonal_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v w : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
          H N hN beta hbeta u v)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
          H N hN beta hbeta w f) = 0 := by
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta v))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta w)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)) = 0
  rw [realL2ExternalTensor_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero,
    mul_zero]

/-- `F ⊠ F` is orthogonal to `K ⊠ K` on decomposable vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTop_inner_orthogonalOrthogonal_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
          H N hN beta hbeta u v)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
          H N hN beta hbeta f g) = 0 := by
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta v))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g)) = 0
  rw [realL2ExternalTensor_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero,
    zero_mul]

/-- `K ⊠ F` is orthogonal to `F ⊠ K` on decomposable vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTop_inner_topOrthogonal_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
          H N hN beta hbeta f u)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
          H N hN beta hbeta v g) = 0 := by
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta v)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g)) = 0
  rw [realL2ExternalTensor_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_inner_topEigenspace_eq_zero,
    zero_mul]

/-- `K ⊠ F` is orthogonal to `K ⊠ K` on decomposable vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTop_inner_orthogonalOrthogonal_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g h : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
          H N hN beta hbeta f u)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
          H N hN beta hbeta g h) = 0 := by
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta h)) = 0
  rw [realL2ExternalTensor_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero,
    mul_zero]

/-- `F ⊠ K` is orthogonal to `K ⊠ K` on decomposable vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonal_inner_orthogonalOrthogonal_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g h : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
          H N hN beta hbeta u f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
          H N hN beta hbeta g h) = 0 := by
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
            H N hN beta hbeta u)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta g)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta h)) = 0
  rw [realL2ExternalTensor_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2_inner_excitation_eq_zero,
    zero_mul]

end

end MathlibAnalytic
end MGAP4D
