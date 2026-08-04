import Mathlib.Analysis.InnerProductSpace.PiL2
import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanReversibility
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Standard Euclidean carrier for observables on a finite product space after
multiplication by the square root of a positive weight. -/
abbrev FinitePositiveWeightHilbertSpace
    (ι G : Type)
    [Fintype ι]
    [Fintype G] : Type :=
  EuclideanSpace ℝ (ι → G)

/-- Embed an observable as the Euclidean vector `sqrt(weight) * f`. -/
noncomputable def finitePositiveWeightHilbertEmbedLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) :
    ((ι → G) → ℝ) →ₗ[ℝ] FinitePositiveWeightHilbertSpace ι G where
  toFun f :=
    WithLp.toLp 2 fun A : ι → G => Real.sqrt (weight A) * f A
  map_add' f g := by
    ext A
    change Real.sqrt (weight A) * (f A + g A) =
      Real.sqrt (weight A) * f A + Real.sqrt (weight A) * g A
    ring
  map_smul' c f := by
    ext A
    change Real.sqrt (weight A) * (c * f A) =
      c * (Real.sqrt (weight A) * f A)
    ring

@[simp] theorem finitePositiveWeightHilbertEmbedLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G) :
    finitePositiveWeightHilbertEmbedLinearMap weight f A =
      Real.sqrt (weight A) * f A :=
  rfl

/-- Strict positivity of the weight makes every square-root multiplier
nonzero. -/
theorem finitePositiveWeight_sqrt_ne_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G) :
    Real.sqrt (weight A) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (hweight A))

/-- Recover an observable from its positive-weight Euclidean vector. -/
noncomputable def finitePositiveWeightHilbertObserveLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) :
    FinitePositiveWeightHilbertSpace ι G →ₗ[ℝ] ((ι → G) → ℝ) where
  toFun x := fun A => x A / Real.sqrt (weight A)
  map_add' x y := by
    funext A
    change (x A + y A) / Real.sqrt (weight A) =
      x A / Real.sqrt (weight A) + y A / Real.sqrt (weight A)
    ring
  map_smul' c x := by
    funext A
    change (c * x A) / Real.sqrt (weight A) =
      c * (x A / Real.sqrt (weight A))
    ring

@[simp] theorem finitePositiveWeightHilbertObserveLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (x : FinitePositiveWeightHilbertSpace ι G)
    (A : ι → G) :
    finitePositiveWeightHilbertObserveLinearMap weight x A =
      x A / Real.sqrt (weight A) :=
  rfl

/-- Observing an embedded observable recovers the observable. -/
theorem finitePositiveWeightHilbert_observe_embed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightHilbertObserveLinearMap weight
        (finitePositiveWeightHilbertEmbedLinearMap weight f) = f := by
  funext A
  rw [finitePositiveWeightHilbertObserveLinearMap_apply,
    finitePositiveWeightHilbertEmbedLinearMap_apply]
  field_simp [finitePositiveWeight_sqrt_ne_zero weight hweight A]

/-- Embedding a recovered observable returns the original Euclidean vector. -/
theorem finitePositiveWeightHilbert_embed_observe
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (x : FinitePositiveWeightHilbertSpace ι G) :
    finitePositiveWeightHilbertEmbedLinearMap weight
        (finitePositiveWeightHilbertObserveLinearMap weight x) = x := by
  ext A
  rw [finitePositiveWeightHilbertEmbedLinearMap_apply,
    finitePositiveWeightHilbertObserveLinearMap_apply]
  field_simp [finitePositiveWeight_sqrt_ne_zero weight hweight A]

/-- The Euclidean inner product of embedded observables is the unnormalized
positive-weight pairing. -/
theorem finitePositiveWeightHilbert_inner_embed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f g : (ι → G) → ℝ) :
    inner ℝ (finitePositiveWeightHilbertEmbedLinearMap weight f)
        (finitePositiveWeightHilbertEmbedLinearMap weight g) =
      finitePositiveWeightPairing weight f g := by
  classical
  rw [PiLp.inner_apply]
  unfold finitePositiveWeightPairing
  apply Finset.sum_congr
  · ext A
    simp
  · intro A _hA
    change
      inner ℝ
          (Real.sqrt (weight A) * f A)
          (Real.sqrt (weight A) * g A) =
        weight A * f A * g A
    change
      (Real.sqrt (weight A) * g A) *
          (Real.sqrt (weight A) * f A) =
        weight A * f A * g A
    calc
      (Real.sqrt (weight A) * g A) *
          (Real.sqrt (weight A) * f A) =
        (Real.sqrt (weight A)) ^ 2 * f A * g A := by
          ring
      _ = weight A * f A * g A := by
        rw [Real.sq_sqrt (le_of_lt (hweight A))]

/-- The squared Euclidean norm of an embedded observable is its weighted
self-pairing. -/
theorem finitePositiveWeightHilbert_norm_sq_embed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ) :
    ‖finitePositiveWeightHilbertEmbedLinearMap weight f‖ ^ 2 =
      finitePositiveWeightPairing weight f f := by
  calc
    ‖finitePositiveWeightHilbertEmbedLinearMap weight f‖ ^ 2 =
        inner ℝ (finitePositiveWeightHilbertEmbedLinearMap weight f)
          (finitePositiveWeightHilbertEmbedLinearMap weight f) := by
      simpa using
        (real_inner_self_eq_norm_sq
          (finitePositiveWeightHilbertEmbedLinearMap weight f)).symm
    _ = finitePositiveWeightPairing weight f f :=
      finitePositiveWeightHilbert_inner_embed weight hweight f f

/-- The constant-one observable paired on the left gives the weighted first
moment. -/
theorem finitePositiveWeightPairing_one_left
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight (fun _ : ι → G => (1 : ℝ)) f =
      finitePositiveWeightSum weight f := by
  classical
  unfold finitePositiveWeightPairing finitePositiveWeightSum
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Positive-weight vacuum vector represented by the constant-one observable. -/
noncomputable def finitePositiveWeightHilbertVacuum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) :
    FinitePositiveWeightHilbertSpace ι G :=
  finitePositiveWeightHilbertEmbedLinearMap weight
    (fun _ : ι → G => (1 : ℝ))

/-- Vacuum pairing with an embedded observable is its weighted first moment. -/
theorem finitePositiveWeightHilbert_inner_vacuum_embed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ) :
    inner ℝ (finitePositiveWeightHilbertVacuum weight)
        (finitePositiveWeightHilbertEmbedLinearMap weight f) =
      finitePositiveWeightSum weight f := by
  rw [finitePositiveWeightHilbertVacuum,
    finitePositiveWeightHilbert_inner_embed weight hweight,
    finitePositiveWeightPairing_one_left]

/-- Exact one-site conditional expectation fixes the constant-one observable. -/
theorem finitePositiveWeightSingleSiteExpectation_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G)
    (e : ι) :
    finitePositiveWeightSingleSiteExpectation weight
        (fun _ : ι → G => (1 : ℝ)) A e = 1 := by
  unfold finitePositiveWeightSingleSiteExpectation
  simpa using
    finitePositiveWeightSingleSiteProbability_sum_eq_one
      weight hweight A e

/-- For a nonempty coordinate set, uniform random scan fixes constants. -/
theorem finitePositiveWeightRandomScan_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) :
    finitePositiveWeightRandomScanConditionalExpectation weight
        (fun _ : ι → G => (1 : ℝ)) =
      (fun _ : ι → G => (1 : ℝ)) := by
  funext A
  unfold finitePositiveWeightRandomScanConditionalExpectation
  simp_rw [finitePositiveWeightSingleSiteExpectation_one weight hweight]
  have hCardNe : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  simp [hCardNe]

/-- Random scan transported to the Euclidean positive-weight Hilbert carrier. -/
noncomputable def finitePositiveWeightHilbertRandomScanLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) :
    FinitePositiveWeightHilbertSpace ι G →ₗ[ℝ]
      FinitePositiveWeightHilbertSpace ι G :=
  (finitePositiveWeightHilbertEmbedLinearMap weight).comp
    ((finitePositiveWeightRandomScanLinearMap weight).comp
      (finitePositiveWeightHilbertObserveLinearMap weight))

@[simp] theorem finitePositiveWeightHilbertRandomScanLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (x : FinitePositiveWeightHilbertSpace ι G) :
    finitePositiveWeightHilbertRandomScanLinearMap weight x =
      finitePositiveWeightHilbertEmbedLinearMap weight
        (finitePositiveWeightRandomScanConditionalExpectation weight
          (finitePositiveWeightHilbertObserveLinearMap weight x)) := by
  simp [finitePositiveWeightHilbertRandomScanLinearMap]

/-- The transported random-scan operator intertwines with embedding. -/
theorem finitePositiveWeightHilbertRandomScanLinearMap_embed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightHilbertRandomScanLinearMap weight
        (finitePositiveWeightHilbertEmbedLinearMap weight f) =
      finitePositiveWeightHilbertEmbedLinearMap weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) := by
  rw [finitePositiveWeightHilbertRandomScanLinearMap_apply,
    finitePositiveWeightHilbert_observe_embed weight hweight f]

/-- Detailed balance makes the transported random-scan operator symmetric. -/
theorem finitePositiveWeightHilbertRandomScanLinearMap_isSymmetric
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    (finitePositiveWeightHilbertRandomScanLinearMap weight).IsSymmetric := by
  intro x y
  calc
    inner ℝ (finitePositiveWeightHilbertRandomScanLinearMap weight x) y =
      inner ℝ
        (finitePositiveWeightHilbertRandomScanLinearMap weight
          (finitePositiveWeightHilbertEmbedLinearMap weight
            (finitePositiveWeightHilbertObserveLinearMap weight x)))
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight y)) := by
      rw [finitePositiveWeightHilbert_embed_observe weight hweight x,
        finitePositiveWeightHilbert_embed_observe weight hweight y]
    _ = inner ℝ
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightRandomScanConditionalExpectation weight
            (finitePositiveWeightHilbertObserveLinearMap weight x)))
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight y)) := by
      rw [finitePositiveWeightHilbertRandomScanLinearMap_embed weight hweight]
    _ = finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight
          (finitePositiveWeightHilbertObserveLinearMap weight x))
        (finitePositiveWeightHilbertObserveLinearMap weight y) :=
      finitePositiveWeightHilbert_inner_embed weight hweight _ _
    _ = finitePositiveWeightPairing weight
        (finitePositiveWeightHilbertObserveLinearMap weight x)
        (finitePositiveWeightRandomScanConditionalExpectation weight
          (finitePositiveWeightHilbertObserveLinearMap weight y)) :=
      finitePositiveWeightRandomScan_pairing_symm weight _ _
    _ = inner ℝ
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight x))
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightRandomScanConditionalExpectation weight
            (finitePositiveWeightHilbertObserveLinearMap weight y))) :=
      (finitePositiveWeightHilbert_inner_embed weight hweight _ _).symm
    _ = inner ℝ
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight x))
        (finitePositiveWeightHilbertRandomScanLinearMap weight
          (finitePositiveWeightHilbertEmbedLinearMap weight
            (finitePositiveWeightHilbertObserveLinearMap weight y))) := by
      rw [finitePositiveWeightHilbertRandomScanLinearMap_embed weight hweight]
    _ = inner ℝ x
        (finitePositiveWeightHilbertRandomScanLinearMap weight y) := by
      rw [finitePositiveWeightHilbert_embed_observe weight hweight x,
        finitePositiveWeightHilbert_embed_observe weight hweight y]

/-- The transported random-scan operator fixes the positive-weight vacuum. -/
theorem finitePositiveWeightHilbertRandomScanLinearMap_vacuum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) :
    finitePositiveWeightHilbertRandomScanLinearMap weight
        (finitePositiveWeightHilbertVacuum weight) =
      finitePositiveWeightHilbertVacuum weight := by
  rw [finitePositiveWeightHilbertVacuum,
    finitePositiveWeightHilbertRandomScanLinearMap_embed weight hweight,
    finitePositiveWeightRandomScan_one weight hweight hCard]

/-- Symmetry and vacuum preservation imply invariance of the weighted-centered
Hilbert sector. -/
theorem finitePositiveWeightHilbertRandomScan_preserves_vacuumOrthogonal
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (x : FinitePositiveWeightHilbertSpace ι G)
    (hx : x ∈ finiteVacuumOrthogonal
      (finitePositiveWeightHilbertVacuum weight)) :
    finitePositiveWeightHilbertRandomScanLinearMap weight x ∈
      finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) := by
  rw [finite_wilson_mem_vacuumOrthogonal_iff]
  have hOrth :
      inner ℝ (finitePositiveWeightHilbertVacuum weight) x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      (finitePositiveWeightHilbertVacuum weight) x).mp hx
  calc
    inner ℝ (finitePositiveWeightHilbertVacuum weight)
        (finitePositiveWeightHilbertRandomScanLinearMap weight x) =
      inner ℝ (finitePositiveWeightHilbertRandomScanLinearMap weight x)
        (finitePositiveWeightHilbertVacuum weight) := real_inner_comm _ _
    _ = inner ℝ x
        (finitePositiveWeightHilbertRandomScanLinearMap weight
          (finitePositiveWeightHilbertVacuum weight)) :=
      finitePositiveWeightHilbertRandomScanLinearMap_isSymmetric
        weight hweight x (finitePositiveWeightHilbertVacuum weight)
    _ = inner ℝ x (finitePositiveWeightHilbertVacuum weight) := by
      rw [finitePositiveWeightHilbertRandomScanLinearMap_vacuum
        weight hweight hCard]
    _ = inner ℝ (finitePositiveWeightHilbertVacuum weight) x :=
      real_inner_comm _ _
    _ = 0 := hOrth

/-- Restriction of positive-weight random scan to the weighted-centered Hilbert
sector. -/
noncomputable def finitePositiveWeightHilbertRandomScanRestrictedLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) :
    finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) →ₗ[ℝ]
      finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) :=
  (finitePositiveWeightHilbertRandomScanLinearMap weight).restrict
    (finitePositiveWeightHilbertRandomScan_preserves_vacuumOrthogonal
      weight hweight hCard)

/-- The centered restriction remains symmetric. -/
theorem finitePositiveWeightHilbertRandomScanRestrictedLinearMap_isSymmetric
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) :
    (finitePositiveWeightHilbertRandomScanRestrictedLinearMap
      weight hweight hCard).IsSymmetric :=
  (finitePositiveWeightHilbertRandomScanLinearMap_isSymmetric
    weight hweight).restrict_invariant
      (finitePositiveWeightHilbertRandomScan_preserves_vacuumOrthogonal
        weight hweight hCard)

end

end MathlibAnalytic
end MGAP4D
