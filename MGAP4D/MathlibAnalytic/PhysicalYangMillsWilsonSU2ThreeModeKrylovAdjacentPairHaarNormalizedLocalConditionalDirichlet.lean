import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarLocalPairDirichlet
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-!
# P4-Q2-AS: exact normalized one-link Wilson conditional Haar Dirichlet form

AR supplies the EXACT multiplicative factor of the original one-slab SU(N)
Wilson kernel under a replacement of one right-boundary link. Its logarithm
depends only on the crossing term and the adjacent spatial plaquettes, with
absolute increment at most 8, uniformly in finite lattice volume H.

Here we integrate that REAL Wilson local factor against the original
normalized compact SU(N) Haar probability (not a frozen posterior receiver).
We construct the positive partition Z, the genuine normalized local density
rho=w/Z, and the tilted single-link conditional Haar probability measure.
All are concrete and remain defined for any beta>=0 and any finite H.

  exp(-8 beta) <= Z <= exp(8 beta)
  exp(-16 beta) <= rho(g) <= exp(16 beta),  int rho dHaar = 1
  exp(-32 beta) * E_HaarPair[(phi(g)-phi(h))²]
      <= E_rhoPair[(phi(g)-phi(h))²].

This is a VOLUME-INDEPENDENT one-link conditional Dirichlet comparison, not
a uniform gap of the complete physical time-transfer, and the normalized
one-link raw Wilson conditional must not be conflated with the actual
ground-state posterior fiber (which includes variable top-vacuum weights).
No surrogate Gram, no Dobrushin, no extra axiom/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4ASGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ASCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ASSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ASMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ASBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ASLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Continuity of a right one-link update, without changing any off-target
coordinate of the actual spatial-slice SU(N) configuration. -/
theorem periodicHypercubicEvenSpecialUnitaryRightLinkUpdate_continuous
    (H N : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Function.update B target g) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e = target
  · subst e
    simpa [Function.update] using
      (continuous_id' :
        Continuous (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => g))
  · simpa [Function.update, he] using
      (continuous_const :
        Continuous (fun _g : Matrix.specialUnitaryGroup (Fin N) ℂ => B e))

/-- A generic cancellation lemma: an exact factor of a continuously
varying kernel by a NONZERO fixed reference weight is continuous. Keeping
this theorem abstract avoids unfolding the large concrete Wilson kernel
during Lean's reducibility and instance-synthesis normalization. -/
theorem p4Q2AS_continuous_factor_of_kernel_mul
    {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    (K : X → ℝ) (F : G → X) (w : G → ℝ) (k0 : ℝ)
    (hK : Continuous K) (hF : Continuous F)
    (hk0 : k0 ≠ 0)
    (hFactor : ∀ g, K (F g) = w g * k0) :
    Continuous w := by
  have hIdentity : w = (fun g => K (F g) / k0) := by
    funext g
    exact (eq_div_iff hk0).2 (hFactor g).symm
  rw [hIdentity]
  exact (hK.comp hF).div_const _

/-- The genuine relative Wilson right-link factor is continuous in the
new SU(N) link. The literal kernel factorization is passed only to the
already-checked generic cancellation lemma. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_continuous
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g) := by
  let K := fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
     periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2
  let F := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    (A, Function.update B target g)
  let w := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
  let k0 := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    H N beta A B
  have hK : Continuous K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta
  have hF : Continuous F :=
    continuous_const.prodMk
      (periodicHypercubicEvenSpecialUnitaryRightLinkUpdate_continuous
        H N B target)
  have hk0 : k0 ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta A B).ne'
  have hFactor : ∀ g, K (F g) = w g * k0 := by
    intro g
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta A B target g
  change Continuous w
  exact p4Q2AS_continuous_factor_of_kernel_mul
    K F w k0 hK hF hk0 hFactor

/-- Actual Wilson local multiplier is Haar integrable on the compact SU(N)
link group. There is no auxiliary finite or proxy state space. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_integrable
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Integrable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_continuous
      H N beta A B target).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- EXACT finite Wilson one-link partition relative to unchanged right
background B. This normalization involves only one SU(N) Haar coordinate. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- The exact local Haar partition is bounded independently of H. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_bounds
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Real.exp (-8 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
        H N beta A B target ∧
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
        H N beta A B target ≤ Real.exp (8 * beta) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hw : Integrable w μ :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_integrable
      H N beta A B target
  have hlower : ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      Real.exp (-8 * beta) ≤ w g :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta A B target
  have hupper : ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      w g ≤ Real.exp (8 * beta) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B target
  constructor
  · change Real.exp (-8 * beta) ≤ ∫ g, w g ∂μ
    calc
      Real.exp (-8 * beta) =
          ∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ,
            Real.exp (-8 * beta) ∂μ := by simp
      _ ≤ ∫ g, w g ∂μ :=
        integral_mono (integrable_const _) hw hlower
  · change (∫ g, w g ∂μ) ≤ Real.exp (8 * beta)
    calc
      (∫ g, w g ∂μ) ≤
          ∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ,
            Real.exp (8 * beta) ∂μ :=
        integral_mono hw (integrable_const _) hupper
      _ = Real.exp (8 * beta) := by simp

/-- Positive, finite, genuine single-link normalization, without requiring
a positive total-volume kernel minorization. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_pos
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
      H N beta A B target :=
  lt_of_lt_of_le (Real.exp_pos _)
    (periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_bounds
      H N hN beta hbeta A B target).1

/-- Exact single-link raw Wilson Haar conditional DENSITY, as opposed to
the distinct posterior fiber density involving ground-state eigenvectors. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g /
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
      H N beta A B target

theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_continuous
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
      H N beta A B target) := by
  unfold periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
  exact (periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_continuous
    H N beta A B target).div_const _

/-- The normalized Wilson one-link density has total Haar mass exactly one. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_integral_one
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
        H N beta A B target g
      ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) = 1 := by
  have hpos :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_pos
      H N hN beta hbeta A B target
  unfold periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
  rw [integral_div]
  change
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
      H N beta A B target /
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
      H N beta A B target = 1
  exact div_self hpos.ne'

/-- The actual normalized Wilson one-link density is uniformly sandwiched
between exp(-16 beta) and exp(16 beta), with NO total-volume factor. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_bounds
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-16 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
        H N beta A B target g ∧
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
        H N beta A B target g ≤ Real.exp (16 * beta) := by
  let w := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B target g
  let Z := periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition
    H N beta A B target
  have hZpos : 0 < Z :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_pos
      H N hN beta hbeta A B target
  have hZ :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarPartition_bounds
      H N hN beta hbeta A B target
  have hWlower : Real.exp (-8 * beta) ≤ w :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta A B target g
  have hWupper : w ≤ Real.exp (8 * beta) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B target g
  change Real.exp (-16 * beta) ≤ w / Z ∧
    w / Z ≤ Real.exp (16 * beta)
  constructor
  · apply (le_div_iff₀ hZpos).2
    calc
      Real.exp (-16 * beta) * Z ≤
          Real.exp (-16 * beta) * Real.exp (8 * beta) :=
        mul_le_mul_of_nonneg_left hZ.2 (Real.exp_pos _).le
      _ = Real.exp (-8 * beta) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ w := hWlower
  · apply (div_le_iff₀ hZpos).2
    calc
      w ≤ Real.exp (8 * beta) := hWupper
      _ = Real.exp (16 * beta) * Real.exp (-8 * beta) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (16 * beta) * Z :=
        mul_le_mul_of_nonneg_left hZ.1 (Real.exp_pos _).le

/-- The TRUE Wilson one-link log weight: log of its exact positive
Boltzmann multiplier; therefore exp(logWeight)=the original multiplier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.log
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g)

theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight_exp
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
      H N beta A B target g) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g := by
  unfold periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
  exact Real.exp_log
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta A B target g)

/-- Actual raw Wilson conditional Haar probability measure on this one-link
fiber, as Mathlib's exact exponentially tilted compact Haar measure. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).tilted
    (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
      H N beta A B target)

/-- The exact one-link Wilson conditional Haar law is a probability measure,
without assuming any global physical-mass gap or posterior disintegration. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_probability
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
        H N beta A B target) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
  have hInt : Integrable w μ :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalFactor_integrable
      H N beta A B target
  have hExp : (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Real.exp
        (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
          H N beta A B target g)) = w := by
    funext g
    exact periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight_exp
      H N beta A B target g
  have hTiltInt : Integrable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Real.exp
          (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
            H N beta A B target g)) μ := by
    rw [hExp]
    exact hInt
  change IsProbabilityMeasure
    (μ.tilted
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
        H N beta A B target))
  exact MeasureTheory.isProbabilityMeasure_tilted hTiltInt

/-- The exact SU(N) raw Wilson conditional measure has precisely the named
real normalized local density, NOT an auxiliary formal probability kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_eq_withDensity
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
        H N beta A B target =
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).withDensity
        (fun g => ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
            H N beta A B target g)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g
  have hExp : (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Real.exp
        (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
          H N beta A B target g)) = w := by
    funext g
    exact periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight_exp
      H N beta A B target g
  have hInt : (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
      Real.exp
        (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
          H N beta A B target g) ∂μ) = ∫ g, w g ∂μ := by
    rw [hExp]
  change μ.withDensity (fun g =>
      ENNReal.ofReal
        (Real.exp
          (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
            H N beta A B target g) /
          (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
            Real.exp
              (periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight
                H N beta A B target g) ∂μ))) =
    μ.withDensity (fun g =>
      ENNReal.ofReal (w g / (∫ g, w g ∂μ)))
  congr 1
  funext g
  rw [periodicHypercubicEvenSpecialUnitaryRightTargetLocalLogWeight_exp, hInt]

/-- Exactly normalized two-copy local Dirichlet energy for a TRUE SU(N) Haar
one-link test function, expressed in the raw Wilson conditional density. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalPairDirichlet
    (H N : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) : ℝ :=
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let rho := periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
    H N beta A B target
  ∫ p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ,
    rho p.1 * rho p.2 * (phi p.1 - phi p.2) ^ 2 ∂(μ.prod μ)

/-- TWO-COPY LOCAL WILSON DIRICHLET energy controls the original Haar
reference Dirichlet integral with volume-independent e^(-32 beta).
No claim of a gap of the global spatial physical transfer is involved. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalPairDirichlet_lower
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : Continuous phi) :
    Real.exp (-32 * beta) *
        (∫ p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
                 Matrix.specialUnitaryGroup (Fin N) ℂ,
          (phi p.1 - phi p.2) ^ 2
          ∂((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).prod
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) ≤
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalPairDirichlet
        H N beta A B target phi := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let rho := periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
    H N beta A B target
  have hRho : Continuous rho :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_continuous
      H N beta A B target
  have hDiff : Continuous
      (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
          phi p.1 - phi p.2) :=
    (hphi.comp continuous_fst).sub (hphi.comp continuous_snd)
  have hSq : Continuous
      (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
          (phi p.1 - phi p.2) ^ 2) := hDiff.pow 2
  have hProd : Continuous
      (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ => rho p.1 * rho p.2) :=
    (hRho.comp continuous_fst).mul (hRho.comp continuous_snd)
  have hLeftInt : Integrable
      (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Real.exp (-32 * beta) * (phi p.1 - phi p.2) ^ 2) (μ.prod μ) :=
    (continuous_const.mul hSq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRightInt : Integrable
      (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
          rho p.1 * rho p.2 * (phi p.1 - phi p.2) ^ 2) (μ.prod μ) :=
    (hProd.mul hSq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint : ∀ p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ,
      Real.exp (-32 * beta) * (phi p.1 - phi p.2) ^ 2 ≤
        rho p.1 * rho p.2 * (phi p.1 - phi p.2) ^ 2 := by
    intro p
    have hOne :=
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_bounds
        H N hN beta hbeta A B target p.1).1
    have hTwo :=
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_bounds
        H N hN beta hbeta A B target p.2).1
    have hFirstNonneg : 0 ≤ rho p.1 :=
      le_trans (Real.exp_pos _).le hOne
    have hPair : Real.exp (-32 * beta) ≤ rho p.1 * rho p.2 := by
      have hMul : Real.exp (-16 * beta) * Real.exp (-16 * beta) ≤
          rho p.1 * rho p.2 := by
        calc
          Real.exp (-16 * beta) * Real.exp (-16 * beta) ≤
              rho p.1 * Real.exp (-16 * beta) :=
            mul_le_mul_of_nonneg_right hOne (Real.exp_pos _).le
          _ ≤ rho p.1 * rho p.2 :=
            mul_le_mul_of_nonneg_left hTwo hFirstNonneg
      calc
        Real.exp (-32 * beta) =
            Real.exp (-16 * beta) * Real.exp (-16 * beta) := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ ≤ rho p.1 * rho p.2 := hMul
    exact mul_le_mul_of_nonneg_right hPair (sq_nonneg _)
  have hIntegral := integral_mono hLeftInt hRightInt hPoint
  change
    Real.exp (-32 * beta) *
      (∫ p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ,
          (phi p.1 - phi p.2) ^ 2 ∂(μ.prod μ)) ≤
      (∫ p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ,
          rho p.1 * rho p.2 * (phi p.1 - phi p.2) ^ 2 ∂(μ.prod μ))
  rw [integral_const_mul] at hIntegral
  exact hIntegral

end
end MathlibAnalytic
end MGAP4D
