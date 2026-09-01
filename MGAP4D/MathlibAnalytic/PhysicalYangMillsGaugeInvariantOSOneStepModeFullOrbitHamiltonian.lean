import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOneStepModeDyadicOrbit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialSemigroupModeGenerator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The dyadic mesh is strictly positive at every finite level. -/
theorem dyadicUnitTime_pos (n : ℕ) : 0 < dyadicUnitTime n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [dyadicUnitTime] using
        div_pos ih (by norm_num : (0 : NNReal) < 2)

/-- The recursively defined dyadic mesh is the usual geometric sequence. -/
theorem dyadicUnitTime_eq_pow (n : ℕ) :
    dyadicUnitTime n = (1 / 2 : NNReal) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [dyadicUnitTime, ih, pow_succ, div_eq_mul_inv]

/-- The dyadic mesh tends to zero. -/
theorem tendsto_dyadicUnitTime_zero :
    Tendsto dyadicUnitTime atTop (𝓝 0) := by
  have hpow :
      dyadicUnitTime = fun n : ℕ => (1 / 2 : NNReal) ^ n := by
    funext n
    exact dyadicUnitTime_eq_pow n
  rw [hpow]
  exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (1 / 2 : NNReal) < 1)

/-- The lower dyadic index at mesh level `n`. -/
def dyadicFloorIndex (t : NNReal) (n : ℕ) : ℕ :=
  ⌊(t : ℝ) / (dyadicUnitTime n : ℝ)⌋₊

/-- The lower dyadic approximation to a nonnegative Euclidean time. -/
def dyadicFloorTime (t : NNReal) (n : ℕ) : NNReal :=
  dyadicFloorIndex t n • dyadicUnitTime n

/-- The lower dyadic approximation never overshoots its target time. -/
theorem dyadicFloorTime_le (t : NNReal) (n : ℕ) :
    dyadicFloorTime t n ≤ t := by
  have hu : 0 < (dyadicUnitTime n : ℝ) := by
    exact_mod_cast dyadicUnitTime_pos n
  have hfloor :
      (dyadicFloorIndex t n : ℝ) ≤
        (t : ℝ) / (dyadicUnitTime n : ℝ) := by
    exact Nat.floor_le (div_nonneg t.coe_nonneg hu.le)
  have hreal :
      (dyadicFloorIndex t n : ℝ) * (dyadicUnitTime n : ℝ) ≤ (t : ℝ) := by
    calc
      (dyadicFloorIndex t n : ℝ) * (dyadicUnitTime n : ℝ) ≤
          ((t : ℝ) / (dyadicUnitTime n : ℝ)) *
            (dyadicUnitTime n : ℝ) :=
        mul_le_mul_of_nonneg_right hfloor hu.le
      _ = (t : ℝ) := div_mul_cancel₀ _ hu.ne'
  rw [dyadicFloorTime, nsmul_eq_mul]
  exact_mod_cast hreal

/-- The target time lies less than one mesh width above its lower dyadic
approximation. -/
theorem lt_dyadicFloorTime_add_unit (t : NNReal) (n : ℕ) :
    t < dyadicFloorTime t n + dyadicUnitTime n := by
  have hu : 0 < (dyadicUnitTime n : ℝ) := by
    exact_mod_cast dyadicUnitTime_pos n
  have hfloor :
      (t : ℝ) / (dyadicUnitTime n : ℝ) <
        (dyadicFloorIndex t n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hreal :
      (t : ℝ) <
        (dyadicFloorIndex t n : ℝ) * (dyadicUnitTime n : ℝ) +
          (dyadicUnitTime n : ℝ) := by
    calc
      (t : ℝ) =
          ((t : ℝ) / (dyadicUnitTime n : ℝ)) *
            (dyadicUnitTime n : ℝ) := (div_mul_cancel₀ _ hu.ne').symm
      _ < ((dyadicFloorIndex t n : ℝ) + 1) *
            (dyadicUnitTime n : ℝ) :=
        mul_lt_mul_of_pos_right hfloor hu
      _ = (dyadicFloorIndex t n : ℝ) * (dyadicUnitTime n : ℝ) +
            (dyadicUnitTime n : ℝ) := by ring
  rw [dyadicFloorTime, nsmul_eq_mul]
  exact_mod_cast hreal

/-- The distance from the lower dyadic approximation is bounded by one mesh
width. -/
theorem dist_dyadicFloorTime_le (t : NNReal) (n : ℕ) :
    dist (dyadicFloorTime t n) t ≤ (dyadicUnitTime n : ℝ) := by
  rw [NNReal.dist_eq]
  have hle := dyadicFloorTime_le t n
  have hleReal :
      (dyadicFloorTime t n : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hle
  rw [abs_of_nonpos (sub_nonpos.mpr hleReal)]
  have hlt := lt_dyadicFloorTime_add_unit t n
  have hltReal :
      (t : ℝ) <
        (dyadicFloorTime t n : ℝ) + (dyadicUnitTime n : ℝ) := by
    exact_mod_cast hlt
  linarith

/-- Lower dyadic approximations converge to every nonnegative Euclidean time. -/
theorem tendsto_dyadicFloorTime (t : NNReal) :
    Tendsto (dyadicFloorTime t) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero
    (fun n => dist_nonneg)
    (fun n => dist_dyadicFloorTime_le t n)
    (NNReal.tendsto_coe.2 tendsto_dyadicUnitTime_zero)

/-- Strong continuity promotes the dyadic one-step spectral law to the full
positive-time orbit.  Thus a strictly positive one-step eigenvalue determines
all Euclidean times, without any infinitesimal generator input. -/
theorem physicalOperator_apply_of_one_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) (mu : ℝ) (hmu : 0 < mu)
    (hOne : T.toPhysicalSemigroup.operator 1 psi = mu • psi)
    (t : NNReal) :
    T.toPhysicalSemigroup.operator t psi =
      Real.exp (Real.log mu * (t : ℝ)) • psi := by
  let a : ℕ → NNReal := dyadicFloorTime t
  have ha : Tendsto a atTop (𝓝 t) := tendsto_dyadicFloorTime t
  have hDyadic : ∀ n : ℕ,
      T.toPhysicalSemigroup.operator (a n) psi =
        Real.exp (Real.log mu * ((a n : NNReal) : ℝ)) • psi := by
    intro n
    simpa [a, dyadicFloorTime] using
      T.physicalOperator_dyadicTime_apply_of_one_eigen
        hSymmetric psi mu hmu hOne (dyadicFloorIndex t n) n
  have hLeft :
      Tendsto
        (fun n : ℕ => T.toPhysicalSemigroup.operator (a n) psi)
        atTop
        (𝓝 (T.toPhysicalSemigroup.operator t psi)) :=
    (T.physicalOrbit_continuous psi).continuousAt.tendsto.comp ha
  have hCoe :
      Tendsto (fun n : ℕ => ((a n : NNReal) : ℝ)) atTop (𝓝 (t : ℝ)) :=
    NNReal.tendsto_coe.2 ha
  have hScalar :
      Tendsto
        (fun n : ℕ => Real.exp (Real.log mu * ((a n : NNReal) : ℝ)))
        atTop
        (𝓝 (Real.exp (Real.log mu * (t : ℝ)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hCoe)
  have hRight :
      Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log mu * ((a n : NNReal) : ℝ)) • psi)
        atTop
        (𝓝 (Real.exp (Real.log mu * (t : ℝ)) • psi)) :=
    hScalar.smul_const psi
  have hRightOnLeft :
      Tendsto
        (fun n : ℕ => T.toPhysicalSemigroup.operator (a n) psi)
        atTop
        (𝓝 (Real.exp (Real.log mu * (t : ℝ)) • psi)) :=
    hRight.congr' (Eventually.of_forall fun n => (hDyadic n).symm)
  exact tendsto_nhds_unique hLeft hRightOnLeft

/-- A positive one-step semigroup eigenvalue already generates the graph-closed
OS Hamiltonian eigenvalue `-log mu`. -/
theorem closedRightHamiltonian_apply_of_one_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) (mu : ℝ) (hmu : 0 < mu)
    (hOne : T.toPhysicalSemigroup.operator 1 psi = mu • psi) :
    T.closedRightHamiltonian
        ⟨psi,
          T.exponential_orbit_mem_closedRightHamiltonianDomain
            psi (-Real.log mu) (by
              intro t
              simpa using
                T.physicalOperator_apply_of_one_eigen
                  hSymmetric psi mu hmu hOne t)⟩ =
      (-Real.log mu) • psi := by
  apply T.closedRightHamiltonian_apply_of_exponential_orbit
  intro t
  simpa using
    T.physicalOperator_apply_of_one_eigen hSymmetric psi mu hmu hOne t

/-- On the physical excitation carrier, one positive one-step eigenvalue is
sufficient to produce the restricted closed-Hamiltonian mode with energy
`-log mu`.  All domain and infinitesimal-generator facts are generated. -/
theorem vacuumOrthogonalClosedRightHamiltonian_apply_of_one_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert) (mu : ℝ) (hmu : 0 < mu)
    (hOne :
      T.toPhysicalSemigroup.operator 1 (psi : P.PhysicalHilbert) =
        mu • (psi : P.PhysicalHilbert)) :
    T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric
        ⟨psi,
          T.exponential_orbit_mem_vacuumOrthogonalClosedRightHamiltonianDomain
            psi (-Real.log mu) (by
              intro t
              simpa using
                T.physicalOperator_apply_of_one_eigen
                  hInnerSymmetric (psi : P.PhysicalHilbert) mu hmu hOne t)⟩ =
      (-Real.log mu) • psi := by
  apply T.vacuumOrthogonalClosedRightHamiltonian_apply_of_exponential_orbit
  intro t
  simpa using
    T.physicalOperator_apply_of_one_eigen
      hInnerSymmetric (psi : P.PhysicalHilbert) mu hmu hOne t

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
