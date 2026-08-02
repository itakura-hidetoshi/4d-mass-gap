import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductEncodingCore
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Every member of a finite list of natural numbers lies below its folded
maximum. -/
theorem continuousLinearMapJointRemainderNat_le_foldrMax_of_mem
    {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    n ≤ ns.foldr max 0 := by
  induction ns with
  | nil => simp at hn
  | cons a ns ih =>
      rcases List.mem_cons.mp hn with rfl | hn
      · exact le_max_left _ _
      · exact le_trans (ih hn) (le_max_right _ _)

/-- A folded maximum is below `N` exactly when every list member is below
`N`. -/
theorem continuousLinearMapJointRemainderNat_foldrMax_le_iff
    (ns : List ℕ) (N : ℕ) :
    ns.foldr max 0 ≤ N ↔ ∀ n ∈ ns, n ≤ N := by
  induction ns with
  | nil => simp
  | cons a ns ih =>
      simp [ih, max_le_iff]

/-- The maximum of a finite type-indexed family of natural numbers. -/
noncomputable def continuousLinearMapJointRemainderFiniteMaximum
    {ι : Type*} [Fintype ι] (f : ι → ℕ) : ℕ :=
  (Finset.univ.toList.map f).foldr max 0

/-- Every coordinate lies below the finite maximum. -/
theorem continuousLinearMapJointRemainder_le_finiteMaximum
    {ι : Type*} [Fintype ι] (f : ι → ℕ) (i : ι) :
    f i ≤ continuousLinearMapJointRemainderFiniteMaximum f := by
  classical
  unfold continuousLinearMapJointRemainderFiniteMaximum
  apply continuousLinearMapJointRemainderNat_le_foldrMax_of_mem
  exact List.mem_map.mpr ⟨i, by simp, rfl⟩

/-- Exact threshold characterization of the finite maximum. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_le_iff
    {ι : Type*} [Fintype ι] (f : ι → ℕ) (N : ℕ) :
    continuousLinearMapJointRemainderFiniteMaximum f ≤ N ↔ ∀ i, f i ≤ N := by
  classical
  unfold continuousLinearMapJointRemainderFiniteMaximum
  rw [continuousLinearMapJointRemainderNat_foldrMax_le_iff]
  simp

/-- Pointwise comparison of finite natural families implies comparison of their
maxima. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_mono
    {ι : Type*} [Fintype ι] {f g : ι → ℕ}
    (hfg : ∀ i, f i ≤ g i) :
    continuousLinearMapJointRemainderFiniteMaximum f ≤
      continuousLinearMapJointRemainderFiniteMaximum g := by
  apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff f _).2
  intro i
  exact le_trans (hfg i)
    (continuousLinearMapJointRemainder_le_finiteMaximum g i)

/-- A finite maximum is invariant under an equivalence of its coordinate
index. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_reindex_eq
    {ι : Type*} [Fintype ι] (f : ι → ℕ) (e : ι ≃ ι) :
    continuousLinearMapJointRemainderFiniteMaximum (fun i => f (e i)) =
      continuousLinearMapJointRemainderFiniteMaximum f := by
  apply le_antisymm
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _).2
    intro i
    exact continuousLinearMapJointRemainder_le_finiteMaximum f (e i)
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _).2
    intro i
    simpa using
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun j => f (e j)) (e.symm i))

/-- The maximum of all coordinate response safe orders when every coordinate
has its own strict tolerance. -/
noncomputable def continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M : ℝ) (epsilon : ι → ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteMaximum
    (fun i => continuousLinearMapJointRemainderResponseSafeOrder
      (φ i) q M (epsilon i))

/-- Exact threshold characterization of the coordinate-tolerance safe order. -/
theorem continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_le_iff
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M : ℝ) (epsilon : ι → ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon ≤ N ↔
      ∀ i, continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M (epsilon i) ≤ N := by
  exact continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _

/-- One natural number controls a carrier tolerance, a dependent Pi-product
tolerance, every coordinate-specific tolerance, and an independent trace
tolerance. -/
noncomputable def continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  max (continuousLinearMapJointRemainderCarrierSharpOrder
      q M epsilonCarrier)
    (max (continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        q M epsilonProduct)
      (max
        (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
          φ q M epsilonCoordinate)
        (continuousLinearMapJointRemainderTraceSafeOrder
          V q M epsilonTrace)))

/-- Exact threshold characterization of the full vector-tolerance master
order. -/
theorem continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_le_iff
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace ≤ N ↔
      continuousLinearMapJointRemainderCarrierSharpOrder
          q M epsilonCarrier ≤ N ∧
      continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiProductObservable φ)
          q M epsilonProduct ≤ N ∧
      (∀ i, continuousLinearMapJointRemainderResponseSafeOrder
          (φ i) q M (epsilonCoordinate i) ≤ N) ∧
      continuousLinearMapJointRemainderTraceSafeOrder
          V q M epsilonTrace ≤ N := by
  unfold continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
  simp only [max_le_iff]
  rw [continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_le_iff]

/-- The carrier order lies below the vector-tolerance master. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilonCarrier ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  exact le_max_left _ _

/-- The encoded Pi-product response order lies below the vector-tolerance
master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        q M epsilonProduct ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- Every coordinate response order, at its own tolerance, lies below the
vector-tolerance master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M (epsilonCoordinate i) ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  calc
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M (epsilonCoordinate i) ≤
      continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilonCoordinate :=
      continuousLinearMapJointRemainder_le_finiteMaximum _ i
    _ ≤ max
        (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
          φ q M epsilonCoordinate)
        (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace) :=
      le_max_left _ _
    _ ≤ max
        (continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiProductObservable φ)
          q M epsilonProduct)
        (max
          (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
            φ q M epsilonCoordinate)
          (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace)) :=
      le_max_right _ _
    _ ≤ continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace :=
      le_max_right _ _

/-- The trace order lies below the vector-tolerance master. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  calc
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace ≤
      max
        (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
          φ q M epsilonCoordinate)
        (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace) :=
      le_max_right _ _
    _ ≤ max
        (continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiProductObservable φ)
          q M epsilonProduct)
        (max
          (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
            φ q M epsilonCoordinate)
          (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace)) :=
      le_max_right _ _
    _ ≤ continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace :=
      le_max_right _ _

/-- Increasing a response tolerance cannot increase its universally safe
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    {q M epsilon₁ epsilon₂ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon₂ ≤
      continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon₁ := by
  unfold continuousLinearMapJointRemainderResponseSafeOrder
  have hconstant : 0 < (‖φ‖ + 1) * M := by
    exact mul_pos (by linarith [norm_nonneg φ]) hM
  exact geometricDecaySharpTruncationOrder_antitone_epsilon
    hq0 hq1 hconstant hepsilon₁ hepsilon₂ hepsilon

/-- Increasing a trace tolerance cannot increase its safe order. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_antitone_epsilon
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {q M epsilon₁ epsilon₂ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon₂ ≤
      continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon₁ := by
  simpa [continuousLinearMapJointRemainderTraceSafeOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
      (continuousLinearMapTrace (V := V)) hq0 hq1 hM
      hepsilon₁ hepsilon₂ hepsilon

/-- Coordinatewise relaxation of a finite tolerance vector cannot increase the
coordinate safe order. -/
theorem continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_antitone
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    {q M : ℝ} {epsilon₁ epsilon₂ : ι → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon₁ : ∀ i, 0 < epsilon₁ i)
    (hepsilon₂ : ∀ i, 0 < epsilon₂ i)
    (hepsilon : ∀ i, epsilon₁ i ≤ epsilon₂ i) :
    continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon₂ ≤
      continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon₁ := by
  apply continuousLinearMapJointRemainderFiniteMaximum_mono
  intro i
  exact continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
    (φ i) hq0 hq1 hM (hepsilon₁ i) (hepsilon₂ i) (hepsilon i)

/-- Relaxing any or all four tolerance channels cannot increase the common
master order. -/
theorem continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_antitone
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    {q M epsilonCarrier₁ epsilonCarrier₂ epsilonProduct₁ epsilonProduct₂
      epsilonTrace₁ epsilonTrace₂ : ℝ}
    {epsilonCoordinate₁ epsilonCoordinate₂ : ι → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier₁ : 0 < epsilonCarrier₁) (hCarrier₂ : 0 < epsilonCarrier₂)
    (hProduct₁ : 0 < epsilonProduct₁) (hProduct₂ : 0 < epsilonProduct₂)
    (hCoordinate₁ : ∀ i, 0 < epsilonCoordinate₁ i)
    (hCoordinate₂ : ∀ i, 0 < epsilonCoordinate₂ i)
    (hTrace₁ : 0 < epsilonTrace₁) (hTrace₂ : 0 < epsilonTrace₂)
    (hCarrier : epsilonCarrier₁ ≤ epsilonCarrier₂)
    (hProduct : epsilonProduct₁ ≤ epsilonProduct₂)
    (hCoordinate : ∀ i, epsilonCoordinate₁ i ≤ epsilonCoordinate₂ i)
    (hTrace : epsilonTrace₁ ≤ epsilonTrace₂) :
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier₂ epsilonProduct₂ epsilonCoordinate₂ epsilonTrace₂ ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier₁ epsilonProduct₁ epsilonCoordinate₁ epsilonTrace₁ := by
  unfold continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
  exact max_le_max
    (continuousLinearMapJointRemainderCarrierSharpOrder_antitone_epsilon
      hq0 hq1 hM hCarrier₁ hCarrier₂ hCarrier)
    (max_le_max
      (continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        hq0 hq1 hM hProduct₁ hProduct₂ hProduct)
      (max_le_max
        (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_antitone
          φ hq0 hq1 hM hCoordinate₁ hCoordinate₂ hCoordinate)
        (continuousLinearMapJointRemainderTraceSafeOrder_antitone_epsilon
          V hq0 hq1 hM hTrace₁ hTrace₂ hTrace)))

/-- Every base order above the vector-tolerance master controls all four
certificate channels at their distinct tolerances. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_dependentPiProductToleranceMasterSafeOrder_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder :
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace ≤
          baseOrder)
    (hCarrier : 0 < epsilonCarrier)
    (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCarrier ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonProduct ∧
    (∀ i,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ <
        epsilonCoordinate i) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonTrace := by
  constructor
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend
        q M epsilonCarrier hq0 hq1 hM hperturb hend
        (le_trans
          (continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
            φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
          hbaseOrder)
        hCarrier
  constructor
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend
        q M epsilonProduct hq0 hq1 hM hperturb hend
        (le_trans
          (continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
            φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
          hbaseOrder)
        hProduct
  constructor
  · intro i
    exact
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
        (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
        q M (epsilonCoordinate i) hq0 hq1 hM hperturb hend
        (le_trans
          (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
            φ i q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
          hbaseOrder)
        (hCoordinate i)
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJet_norm_lt_of_safeOrder_le
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend
        q M epsilonTrace hq0 hq1 hM hperturb hend
        (le_trans
          (continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
            φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
          hbaseOrder)
        hTrace

/-- The explicit vector-tolerance master gives simultaneous control without any
further order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_dependentPiProductToleranceMasterSafeOrder
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hCarrier : 0 < epsilonCarrier)
    (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
      φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCarrier ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonProduct ∧
    (∀ i,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) N taylorOrder tailOrder m H ds h Rbase Rend‖ <
        epsilonCoordinate i) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonTrace := by
  dsimp
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_dependentPiProductToleranceMasterSafeOrder_le
      φ
      (continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
      taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
      hq0 hq1 hM hperturb hend le_rfl
      hCarrier hProduct hCoordinate hTrace

/-- Restrict a dependent Pi-product to a finite coordinate subfamily. -/
noncomputable def continuousLinearMapJointRemainderDependentPiRestrictionMap
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (s : Finset ι) :
    (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1) :=
  ContinuousLinearMap.pi (fun i =>
    (ContinuousLinearMap.proj i.1 : (∀ j, W j) →L[ℝ] W i.1))

@[simp] theorem continuousLinearMapJointRemainderDependentPiRestrictionMap_apply
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (s : Finset ι) (x : ∀ i, W i) (i : {i // i ∈ s}) :
    continuousLinearMapJointRemainderDependentPiRestrictionMap s x i = x i.1 := by
  rfl

/-- Finite dependent-product restriction is a contraction. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiRestrictionMap_le_one
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (s : Finset ι) :
    ‖(continuousLinearMapJointRemainderDependentPiRestrictionMap s :
      (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1))‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (continuousLinearMapJointRemainderDependentPiRestrictionMap s :
      (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1))
    zero_le_one
    (fun x => by
      simp only [one_mul]
      rw [pi_norm_le_iff_of_nonneg
        (x := continuousLinearMapJointRemainderDependentPiRestrictionMap s x)
        (r := ‖x‖) (norm_nonneg x)]
      intro i
      simpa using
        ((pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖)
          (norm_nonneg x)).1 le_rfl i.1))

/-- Restricting the encoded observable to a finite subfamily is exactly
postcomposition by the restriction contraction. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiRestrictionMap_comp_observable
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι) :
    (continuousLinearMapJointRemainderDependentPiRestrictionMap s).comp
        (continuousLinearMapJointRemainderDependentPiProductObservable φ) =
      continuousLinearMapJointRemainderDependentPiProductObservable
        (fun i : {i // i ∈ s} => φ i.1) := by
  ext A i
  rfl

/-- The coordinate-tolerance order of a finite subfamily is below the full
coordinate-tolerance order. -/
theorem continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_subfamily_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (s : Finset ι) (q M : ℝ) (epsilon : ι → ℝ) :
    continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        (fun i : {i // i ∈ s} => φ i.1) q M (fun i => epsilon i.1) ≤
      continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon := by
  apply (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_le_iff
    (fun i : {i // i ∈ s} => φ i.1) q M (fun i => epsilon i.1) _).2
  intro i
  exact continuousLinearMapJointRemainder_le_finiteMaximum
    (fun j => continuousLinearMapJointRemainderResponseSafeOrder
      (φ j) q M (epsilon j)) i.1

/-- Restricting to a finite coordinate subfamily cannot increase the full
vector-tolerance master order. -/
theorem continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_subfamily_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (s : Finset ι)
    {q M epsilonCarrier epsilonProduct epsilonTrace : ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hProduct : 0 < epsilonProduct) :
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (fun i : {i // i ∈ s} => φ i.1)
        q M epsilonCarrier epsilonProduct (fun i => epsilonCoordinate i.1)
        epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
  apply max_le_max le_rfl
  apply max_le_max
  · rw [← continuousLinearMapJointRemainderDependentPiRestrictionMap_comp_observable
      φ s]
    exact continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
      (continuousLinearMapJointRemainderDependentPiRestrictionMap s)
      (continuousLinearMapJointRemainderDependentPiProductObservable φ)
      (continuousLinearMapJointRemainder_norm_dependentPiRestrictionMap_le_one s)
      hq0 hq1 hM hProduct
  · exact max_le_max
      (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_subfamily_le
        φ s q M epsilonCoordinate)
      le_rfl

/-- The coordinate-tolerance aggregate is invariant when a homogeneous finite
family and its tolerance vector are reindexed together. -/
theorem continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_reindex_eq
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : Fin n → ℝ) (e : Fin n ≃ Fin n)
    (q M : ℝ) :
    continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        (fun i => φ (e i)) q M (fun i => epsilon (e i)) =
      continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon := by
  exact continuousLinearMapJointRemainderFiniteMaximum_reindex_eq
    (fun i => continuousLinearMapJointRemainderResponseSafeOrder
      (φ i) q M (epsilon i)) e

/-- A homogeneous finite vector-tolerance master order is invariant when both
the observables and the coordinate tolerances are permuted together. -/
theorem continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_reindex_eq
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilonCoordinate : Fin n → ℝ) (e : Fin n ≃ Fin n)
    {q M epsilonCarrier epsilonProduct epsilonTrace : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hProduct : 0 < epsilonProduct) :
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (W := fun _ : Fin n => W) (fun i => φ (e i))
        q M epsilonCarrier epsilonProduct (fun i => epsilonCoordinate (e i))
        epsilonTrace =
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (W := fun _ : Fin n => W) φ
        q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
  rw [continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_reindex_eq
    φ e hq0 hq1 hM hProduct]
  rw [continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_reindex_eq
    φ epsilonCoordinate e q M]

end MathlibAnalytic
end MGAP4D
