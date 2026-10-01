import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNNonconstant
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# Explicit two-mode normalized-Haar orthonormal family on SU(N)

For every N >= 2, the concrete Wilson-energy powers E_W^0 = 1 and E_W^1 = E_W
are linearly independent in normalized-Haar real L2(SU(N)).

The proof is model-facing and uses no abstract dimension argument:

* if s * 1 + t * E_W vanishes in L2, continuity plus full-support Haar turns
  that L2 identity into pointwise equality;
* evaluation at the identity, where E_W = 0, gives s = 0;
* evaluation at the explicit two-negative diagonal witness from #4999, where
  E_W = 4/N > 0, gives t = 0.

Mathlib Gram--Schmidt then theorem-generates an explicit orthonormal pair.
This is the arbitrary-rank replacement for the first two SU(2)-specific
Gram--Schmidt modes.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory
open scoped ENNReal

noncomputable section

local instance sunTwoModeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sunTwoModeHaarMeasure (N : ℕ) :
    Measure.IsHaarMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance sunTwoModeHaarOpenPos (N : ℕ) :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The standard SU(N) Wilson plaquette energy as a continuous real function. -/
noncomputable def specialUnitaryWilsonPlaquetteEnergyContinuous
    (N : ℕ) :
    C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ) :=
  ⟨specialUnitaryWilsonPlaquetteEnergy N,
    continuous_specialUnitaryWilsonPlaquetteEnergy N⟩

/-- The concrete MemLp.toLp Wilson-energy-power vector agrees with the
canonical ContinuousMap.toLp vector for every positive rank. -/
theorem specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_eq_continuousMap_toLp
    {N : ℕ}
    (hN : 0 < N)
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hN k =
      ContinuousMap.toLp
        (E := ℝ) 2
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ℝ
        (specialUnitaryWilsonPlaquetteEnergyContinuous N ^ k) := by
  apply Lp.ext
  filter_upwards
    [specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_coeFn hN k,
     ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (μ := normalizedCompactHaar
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (specialUnitaryWilsonPlaquetteEnergyContinuous N ^ k)] with U hPower hContinuous
  rw [hPower, hContinuous]
  rfl

/-- The first two concrete Wilson-energy powers as a Fin 2 family. -/
noncomputable def specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
    {N : ℕ}
    (hN : 0 < N) :
    Fin 2 → SpecialUnitaryNormalizedHaarL2 N :=
  ![specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hN 0,
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hN 1]

/-- The two concrete Wilson-energy seed modes are linearly independent for
every N >= 2. -/
theorem specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed_linearIndependent
    {N : ℕ}
    (hN : 2 ≤ N) :
    LinearIndependent ℝ
      (specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
        (lt_of_lt_of_le (by norm_num) hN)) := by
  let hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let oneC : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ) := 1
  let energyC : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ) :=
    specialUnitaryWilsonPlaquetteEnergyContinuous N
  rw [show
    specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed hNpos =
      ![specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hNpos 0,
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hNpos 1] by rfl]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0eq :
      specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hNpos 0 =
        ContinuousMap.toLp (E := ℝ) 2 μ ℝ oneC := by
    simpa [μ, oneC, specialUnitaryWilsonPlaquetteEnergyContinuous] using
      specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_eq_continuousMap_toLp
        hNpos 0
  have h1eq :
      specialUnitaryWilsonPlaquetteEnergyPowerHaarL2 hNpos 1 =
        ContinuousMap.toLp (E := ℝ) 2 μ ℝ energyC := by
    simpa [μ, energyC] using
      specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_eq_continuousMap_toLp
        hNpos 1
  have hLp :
      ContinuousMap.toLp (E := ℝ) 2 μ ℝ (s • oneC + t • energyC) =
        ContinuousMap.toLp (E := ℝ) 2 μ ℝ
          (0 : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ)) := by
    rw [map_add, map_smul, map_smul]
    rw [← h0eq, ← h1eq]
    simpa using hst
  have hContinuous :
      s • oneC + t • energyC =
        (0 : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ)) := by
    exact
      (ContinuousMap.toLp_injective
        (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) μ) hLp
  have hAtOne := congrArg
    (fun f : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ) =>
      f (1 : Matrix.specialUnitaryGroup (Fin N) ℂ))
    hContinuous
  have hs : s = 0 := by
    simpa [oneC, energyC, specialUnitaryWilsonPlaquetteEnergyContinuous,
      specialUnitaryWilsonPlaquetteEnergy_one N hNpos] using hAtOne
  have hAtWitness := congrArg
    (fun f : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ) =>
      f (specialUnitaryTwoNegativeDiagonal N hN))
    hContinuous
  have hEnergyPos :
      0 <
        specialUnitaryWilsonPlaquetteEnergy N
          (specialUnitaryTwoNegativeDiagonal N hN) :=
    specialUnitaryWilsonPlaquetteEnergy_twoNegativeDiagonal_pos N hN
  have ht : t = 0 := by
    rw [hs, zero_smul, zero_add] at hAtWitness
    change
      t * specialUnitaryWilsonPlaquetteEnergy N
          (specialUnitaryTwoNegativeDiagonal N hN) = 0 at hAtWitness
    exact (mul_eq_zero.mp hAtWitness).resolve_right (ne_of_gt hEnergyPos)
  exact ⟨hs, ht⟩

/-- The arbitrary-rank theorem-generated orthonormal pair obtained by
Gram--Schmidt from the concrete constant-one and Wilson-energy modes. -/
noncomputable def specialUnitaryWilsonHaarTwoMode
    {N : ℕ}
    (hN : 2 ≤ N) :
    Fin 2 → SpecialUnitaryNormalizedHaarL2 N :=
  InnerProductSpace.gramSchmidtNormed ℝ
    (specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
      (lt_of_lt_of_le (by norm_num) hN))

/-- The concrete two-mode SU(N) Wilson Haar family is orthonormal for every
N >= 2. -/
theorem specialUnitaryWilsonHaarTwoMode_orthonormal
    {N : ℕ}
    (hN : 2 ≤ N) :
    Orthonormal ℝ (specialUnitaryWilsonHaarTwoMode hN) := by
  exact InnerProductSpace.gramSchmidtNormed_orthonormal
    (specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed_linearIndependent hN)

end

end MathlibAnalytic
end MGAP4D
