import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedSector
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelLeftRiesz
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
import Mathlib.Tactic

/-!
# Independent endpoint gauge fixedness descends through the one-slice Gauss projections

For a pair-Haar `L²` kernel `K` fixed by arbitrary independent endpoint
gauge transformations, its Hilbert--Schmidt pairing

`(f,g) ↦ ⟪K, f ⊠ g⟫`

depends only on the one-slice Gauss-law projections of `f` and `g`.

The proof is intrinsic:

* independent pair fixedness gives exact pairing invariance;
* the left and right Fréchet--Riesz representatives are fixed by every
  one-slice gauge pullback;
* therefore both Riesz representatives lie in the one-slice Gauss-law
  physical subspace;
* self-adjointness of Mathlib's orthogonal star projection then lets each
  test factor be replaced by its Gauss projection without changing the
  kernel pairing.

No Haar averaging formula for the Gauss projection is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance independentGaugePairingTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance independentGaugePairingCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance independentGaugePairingSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance independentGaugePairingMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance independentGaugePairingBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance independentGaugePairingSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance independentGaugePairingSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Pullback by the identity one-slice gauge transformation is exactly the
identity on Haar `L²`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_one
    (H N : ℕ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
        H N 1 f = f := by
  apply Lp.ext
  have h :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry_coeFn
      H N 1 f
  filter_upwards [h] with A hA
  simpa using hA

/-- Independent endpoint fixedness makes the Hilbert--Schmidt kernel pairing
invariant under independently transformed test factors. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_invariant
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (gammaPrimary gammaAntipodal :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing K
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N gammaPrimary f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N gammaAntipodal g) =
      realL2HilbertSchmidtKernelPairing K f g := by
  rw [realL2HilbertSchmidtKernelPairing]
  rw [
    periodicHypercubicEvenSpecialUnitaryRealL2ExternalTensor_independentGaugePullback]
  let V :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
      H N gammaPrimary gammaAntipodal
  calc
    inner ℝ K (V (realL2ExternalTensor f g)) =
        inner ℝ (V K) (V (realL2ExternalTensor f g)) := by
      rw [hK gammaPrimary gammaAntipodal]
    _ = inner ℝ K (realL2ExternalTensor f g) :=
      V.inner_map_map K (realL2ExternalTensor f g)

/-- For an independently gauge-fixed pair kernel, every left Riesz
representative is a genuine one-slice Gauss-law physical vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_leftRiesz_mem_GaussLaw
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelLeftRieszVector K g ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
  intro gamma
  apply ext_inner_right ℝ
  intro f
  let U :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H N gamma
  let Uinv :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H N gamma⁻¹
  have hUndo : U (Uinv f) = f := by
    exact
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_apply_inv
        H N gamma f
  calc
    inner ℝ (U (realL2HilbertSchmidtKernelLeftRieszVector K g)) f =
        inner ℝ
          (U (realL2HilbertSchmidtKernelLeftRieszVector K g))
          (U (Uinv f)) := by rw [hUndo]
    _ = inner ℝ (realL2HilbertSchmidtKernelLeftRieszVector K g) (Uinv f) :=
      U.inner_map_map _ _
    _ = realL2HilbertSchmidtKernelPairing K (Uinv f) g :=
      realL2HilbertSchmidtKernelLeftRieszVector_inner K (Uinv f) g
    _ = realL2HilbertSchmidtKernelPairing K f g := by
      have hPair :=
        periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_invariant
          H N K hK gamma⁻¹ 1 f g
      simpa [Uinv] using hPair
    _ = inner ℝ (realL2HilbertSchmidtKernelLeftRieszVector K g) f :=
      (realL2HilbertSchmidtKernelLeftRieszVector_inner K f g).symm

/-- For an independently gauge-fixed pair kernel, every right Riesz
representative is a genuine one-slice Gauss-law physical vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_rightRiesz_mem_GaussLaw
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelRieszVector K f ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
  intro gamma
  apply ext_inner_right ℝ
  intro g
  let U :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H N gamma
  let Uinv :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
      H N gamma⁻¹
  have hUndo : U (Uinv g) = g := by
    exact
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullback_apply_inv
        H N gamma g
  calc
    inner ℝ (U (realL2HilbertSchmidtKernelRieszVector K f)) g =
        inner ℝ
          (U (realL2HilbertSchmidtKernelRieszVector K f))
          (U (Uinv g)) := by rw [hUndo]
    _ = inner ℝ (realL2HilbertSchmidtKernelRieszVector K f) (Uinv g) :=
      U.inner_map_map _ _
    _ = realL2HilbertSchmidtKernelPairing K f (Uinv g) :=
      realL2HilbertSchmidtKernelRieszVector_inner K f (Uinv g)
    _ = realL2HilbertSchmidtKernelPairing K f g := by
      have hPair :=
        periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_invariant
          H N K hK 1 gamma⁻¹ f g
      simpa [Uinv] using hPair
    _ = inner ℝ (realL2HilbertSchmidtKernelRieszVector K f) g :=
      (realL2HilbertSchmidtKernelRieszVector_inner K f g).symm

/-- The first test factor may be replaced by its one-slice Gauss projection
inside the pairing with an independently gauge-fixed pair kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection_left
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing K
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f) g =
      realL2HilbertSchmidtKernelPairing K f g := by
  let r := realL2HilbertSchmidtKernelLeftRieszVector K g
  have hrMem :
      r ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_leftRiesz_mem_GaussLaw
      H N K hK g
  have hrProj :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N r = r :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff
      H N r).2 hrMem
  calc
    realL2HilbertSchmidtKernelPairing K
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f) g =
      inner ℝ r
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f) :=
      (realL2HilbertSchmidtKernelLeftRieszVector_inner
        K
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f)
        g).symm
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N r) f := by
      simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection] using
        (Submodule.inner_starProjection_left_eq_right
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
            H N).toSubmodule r f).symm
    _ = inner ℝ r f := by rw [hrProj]
    _ = realL2HilbertSchmidtKernelPairing K f g :=
      realL2HilbertSchmidtKernelLeftRieszVector_inner K f g

/-- The second test factor may be replaced by its one-slice Gauss projection
inside the pairing with an independently gauge-fixed pair kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection_right
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing K f
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) =
      realL2HilbertSchmidtKernelPairing K f g := by
  let r := realL2HilbertSchmidtKernelRieszVector K f
  have hrMem :
      r ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_rightRiesz_mem_GaussLaw
      H N K hK f
  have hrProj :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N r = r :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff
      H N r).2 hrMem
  calc
    realL2HilbertSchmidtKernelPairing K f
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) =
      inner ℝ r
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) :=
      (realL2HilbertSchmidtKernelRieszVector_inner
        K f
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g)).symm
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N r) g := by
      simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection] using
        (Submodule.inner_starProjection_left_eq_right
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
            H N).toSubmodule r g).symm
    _ = inner ℝ r g := by rw [hrProj]
    _ = realL2HilbertSchmidtKernelPairing K f g :=
      realL2HilbertSchmidtKernelRieszVector_inner K f g

/-- Both independent endpoint test factors may simultaneously be replaced by
their one-slice Gauss-law projections. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing K
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) =
      realL2HilbertSchmidtKernelPairing K f g := by
  calc
    realL2HilbertSchmidtKernelPairing K
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) =
      realL2HilbertSchmidtKernelPairing K f
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) :=
      periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection_left
        H N K hK f
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g)
    _ = realL2HilbertSchmidtKernelPairing K f g :=
      periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection_right
        H N K hK f g

/-- Audit-visible independent-gauge pairing descent package. -/
structure PeriodicHypercubicEvenSpecialUnitaryIndependentGaugeFixedKernelPairingGaussDescentPackage
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K) : Prop where
  leftRieszPhysical :
    ∀ g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      realL2HilbertSchmidtKernelLeftRieszVector K g ∈
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  rightRieszPhysical :
    ∀ f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      realL2HilbertSchmidtKernelRieszVector K f ∈
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  projectedPairing :
    ∀ f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      realL2HilbertSchmidtKernelPairing K
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f)
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) =
        realL2HilbertSchmidtKernelPairing K f g

/-- Construct the independent-gauge pairing descent package. -/
theorem
    periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixedKernelPairingGaussDescentPackage
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)
    (hK :
      ∀ gammaPrimary gammaAntipodal :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairIndependentGaugePullbackLinearIsometry
            H N gammaPrimary gammaAntipodal K =
          K) :
    PeriodicHypercubicEvenSpecialUnitaryIndependentGaugeFixedKernelPairingGaussDescentPackage
      H N K hK :=
  { leftRieszPhysical :=
      periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_leftRiesz_mem_GaussLaw
        H N K hK
    rightRieszPhysical :=
      periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_rightRiesz_mem_GaussLaw
        H N K hK
    projectedPairing :=
      periodicHypercubicEvenSpecialUnitaryIndependentGaugeFixed_kernelPairing_GaussProjection
        H N K hK }

end

end MathlibAnalytic
end MGAP4D
