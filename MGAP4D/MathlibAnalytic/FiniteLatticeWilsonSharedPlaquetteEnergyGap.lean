import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGlobalPlaquetteEnergyGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Plaquettes containing both a target edge and a source edge.  These are the
only target-local plaquette terms that can respond to a source-link update. -/
noncomputable def FiniteLatticeWilsonSystem.sharedPlaquettes
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) : Finset L.Plaquette := by
  classical
  exact Finset.univ.filter fun p =>
    L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source

@[simp] theorem finite_lattice_mem_sharedPlaquettes_iff
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge)
    (p : L.Plaquette) :
    p ∈ L.sharedPlaquettes target source ↔
      L.PlaquetteTouchesEdge p target ∧
        L.PlaquetteTouchesEdge p source := by
  classical
  simp [FiniteLatticeWilsonSystem.sharedPlaquettes]

/-- A shared-plaquette set is bounded by the total finite plaquette count. -/
theorem finite_lattice_sharedPlaquettes_card_le_plaquetteCard
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) :
    (L.sharedPlaquettes target source).card ≤ Fintype.card L.Plaquette := by
  classical
  simpa using Finset.card_le_card
    (Finset.subset_univ (L.sharedPlaquettes target source))

/-- Boundary values of a plaquette not touching `source` are unchanged by a
source update followed by the same target replacement. -/
theorem finite_lattice_targetReplace_sourceReplace_boundary_eq_of_not_touches_source
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source)
    (k : Fin 4) :
    L.replaceLink A target u (L.boundary p k) =
      L.replaceLink (L.replaceLink A source g) target u
        (L.boundary p k) := by
  classical
  by_cases hTarget : L.boundary p k = target
  · rw [hTarget]
    simp [FiniteLatticeWilsonSystem.replaceLink]
  · have hSource : L.boundary p k ≠ source := by
      intro hk
      exact hNotSource ⟨k, hk⟩
    simp [FiniteLatticeWilsonSystem.replaceLink, hTarget, hSource]

/-- A plaquette not touching the updated source has identical holonomy after a
common target replacement. -/
theorem finite_lattice_targetReplace_sourceReplace_holonomy_eq_of_not_touches_source
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteHolonomy (L.replaceLink A target u) p =
      L.plaquetteHolonomy
        (L.replaceLink (L.replaceLink A source g) target u) p := by
  apply finite_lattice_plaquetteHolonomy_congr
  intro k
  exact
    finite_lattice_targetReplace_sourceReplace_boundary_eq_of_not_touches_source
      L A target source u g p hNotSource k

/-- The corresponding plaquette-energy terms are identical. -/
theorem finite_lattice_targetReplace_sourceReplace_energy_eq_of_not_touches_source
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target u) p) =
      L.plaquetteEnergy
        (L.plaquetteHolonomy
          (L.replaceLink (L.replaceLink A source g) target u) p) := by
  rw [finite_lattice_targetReplace_sourceReplace_holonomy_eq_of_not_touches_source
    L A target source u g p hNotSource]

/-- The change of a target-local action under one source update is exactly the
sum over plaquettes shared by the target and source. -/
theorem finite_lattice_targetLocalAction_sub_sourceReplace_eq_sum_shared
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge) :
    L.targetLocalPlaquetteAction (L.replaceLink A target u) target -
        L.targetLocalPlaquetteAction
          (L.replaceLink (L.replaceLink A source g) target u) target =
      ∑ p ∈ L.sharedPlaquettes target source,
        (L.plaquetteEnergy
            (L.plaquetteHolonomy (L.replaceLink A target u) p) -
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (L.replaceLink (L.replaceLink A source g) target u) p)) := by
  classical
  unfold FiniteLatticeWilsonSystem.targetLocalPlaquetteAction
  rw [← Finset.sum_sub_distrib]
  have hSupport :
      (∑ p ∈ L.sharedPlaquettes target source,
          ((if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy (L.replaceLink A target u) p)
            else 0) -
            (if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy
                  (L.replaceLink (L.replaceLink A source g) target u) p)
            else 0))) =
        ∑ p : L.Plaquette,
          ((if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy (L.replaceLink A target u) p)
            else 0) -
            (if L.PlaquetteTouchesEdge p target then
              L.plaquetteEnergy
                (L.plaquetteHolonomy
                  (L.replaceLink (L.replaceLink A source g) target u) p)
            else 0)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _hp hNotShared
    have hNotBoth :
        ¬ (L.PlaquetteTouchesEdge p target ∧
          L.PlaquetteTouchesEdge p source) := by
      intro hBoth
      exact hNotShared
        ((finite_lattice_mem_sharedPlaquettes_iff
          L target source p).2 hBoth)
    by_cases hTarget : L.PlaquetteTouchesEdge p target
    · have hNotSource : ¬ L.PlaquetteTouchesEdge p source := by
        intro hSource
        exact hNotBoth ⟨hTarget, hSource⟩
      have hEnergy :=
        finite_lattice_targetReplace_sourceReplace_energy_eq_of_not_touches_source
          L A target source u g p hNotSource
      simp [hTarget, hEnergy]
    · simp [hTarget]
  rw [← hSupport]
  apply Finset.sum_congr rfl
  intro p hp
  have hTarget :=
    ((finite_lattice_mem_sharedPlaquettes_iff
      L target source p).1 hp).1
  simp [hTarget]

/-- A single shared plaquette contributes at most the exact plaquette-energy
maximum to the absolute target-local action change. -/
theorem finite_lattice_sharedPlaquetteEnergyDifference_abs_le_max
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette) :
    |L.plaquetteEnergy
          (L.plaquetteHolonomy (L.replaceLink A target u) p) -
        L.plaquetteEnergy
          (L.plaquetteHolonomy
            (L.replaceLink (L.replaceLink A source g) target u) p)| ≤
      L.plaquetteEnergyMax := by
  have hLeft0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hRight0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy
      (L.replaceLink (L.replaceLink A source g) target u) p)
  have hLeftMax := finite_lattice_plaquetteEnergy_le_max L
    (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hRightMax := finite_lattice_plaquetteEnergy_le_max L
    (L.plaquetteHolonomy
      (L.replaceLink (L.replaceLink A source g) target u) p)
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- The absolute target-local action response is bounded by the number of
shared plaquettes times the exact plaquette-energy maximum. -/
theorem finite_lattice_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul_energyMax
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge) :
    |L.targetLocalPlaquetteAction (L.replaceLink A target u) target -
        L.targetLocalPlaquetteAction
          (L.replaceLink (L.replaceLink A source g) target u) target| ≤
      ((L.sharedPlaquettes target source).card : ℝ) *
        L.plaquetteEnergyMax := by
  rw [finite_lattice_targetLocalAction_sub_sourceReplace_eq_sum_shared]
  calc
    |∑ p ∈ L.sharedPlaquettes target source,
        (L.plaquetteEnergy
            (L.plaquetteHolonomy (L.replaceLink A target u) p) -
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (L.replaceLink (L.replaceLink A source g) target u) p))| ≤
      ∑ p ∈ L.sharedPlaquettes target source,
        |L.plaquetteEnergy
            (L.plaquetteHolonomy (L.replaceLink A target u) p) -
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (L.replaceLink (L.replaceLink A source g) target u) p)| :=
        finite_abs_sum_le_sum_abs
          (L.sharedPlaquettes target source)
          (fun p =>
            L.plaquetteEnergy
                (L.plaquetteHolonomy (L.replaceLink A target u) p) -
              L.plaquetteEnergy
                (L.plaquetteHolonomy
                  (L.replaceLink (L.replaceLink A source g) target u) p))
    _ ≤ ∑ _p ∈ L.sharedPlaquettes target source,
        L.plaquetteEnergyMax := by
      apply Finset.sum_le_sum
      intro p _hp
      exact finite_lattice_sharedPlaquetteEnergyDifference_abs_le_max
        L A target source u g p
    _ = ((L.sharedPlaquettes target source).card : ℝ) *
        L.plaquetteEnergyMax := by
      simp [nsmul_eq_mul]

/-- Finite values of active shared-plaquette multiplicities. -/
noncomputable def
    FiniteLatticeWilsonSystem.activeSharedPlaquetteCardValues
    (L : FiniteLatticeWilsonSystem) : Finset ℕ := by
  classical
  exact Finset.univ.image fun pair : L.Edge × L.Edge =>
    if pair.2 ∈ L.activePlaquetteNeighbors pair.1 then
      (L.sharedPlaquettes pair.1 pair.2).card
    else 0

/-- The active shared-multiplicity value set is nonempty when the edge type is
nonempty. -/
theorem finite_lattice_activeSharedPlaquetteCardValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.activeSharedPlaquetteCardValues.Nonempty := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨0, ?_⟩
  unfold FiniteLatticeWilsonSystem.activeSharedPlaquetteCardValues
  apply Finset.mem_image.mpr
  exact ⟨(e, e), Finset.mem_univ _, by simp⟩

/-- Exact largest number of plaquettes shared by an active target/source edge
pair. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalActiveSharedPlaquetteMultiplicity
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℕ :=
  L.activeSharedPlaquetteCardValues.max'
    (finite_lattice_activeSharedPlaquetteCardValues_nonempty L hEdge)

/-- Every active target/source shared-plaquette count is bounded by the exact
active multiplicity. -/
theorem finite_lattice_sharedPlaquettes_card_le_canonicalActiveMultiplicity
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target source : L.Edge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    (L.sharedPlaquettes target source).card ≤
      L.canonicalActiveSharedPlaquetteMultiplicity hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActiveSharedPlaquetteMultiplicity
  apply Finset.le_max'
  unfold FiniteLatticeWilsonSystem.activeSharedPlaquetteCardValues
  apply Finset.mem_image.mpr
  exact ⟨(target, source), Finset.mem_univ _, by simp [hActive]⟩

/-- The exact active shared multiplicity is no larger than the total plaquette
count. -/
theorem finite_lattice_canonicalActiveSharedPlaquetteMultiplicity_le_plaquetteCard
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActiveSharedPlaquetteMultiplicity hEdge ≤
      Fintype.card L.Plaquette := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActiveSharedPlaquetteMultiplicity
  apply Finset.max'_le
  intro n hn
  unfold FiniteLatticeWilsonSystem.activeSharedPlaquetteCardValues at hn
  rcases Finset.mem_image.mp hn with ⟨pair, _hpair, rfl⟩
  by_cases hActive : pair.2 ∈ L.activePlaquetteNeighbors pair.1
  · simp only [if_pos hActive]
    exact finite_lattice_sharedPlaquettes_card_le_plaquetteCard
      L pair.1 pair.2
  · simp [hActive]

/-- Refined shared-plaquette action-oscillation scale. -/
def FiniteLatticeWilsonSystem.sharedPlaquetteEnergyActionOscillation
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℝ :=
  2 * (L.canonicalActiveSharedPlaquetteMultiplicity hEdge : ℝ) *
    L.plaquetteEnergyMax

/-- The refined shared-plaquette action scale is nonnegative. -/
theorem finite_lattice_sharedPlaquetteEnergyActionOscillation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ L.sharedPlaquetteEnergyActionOscillation hEdge := by
  unfold FiniteLatticeWilsonSystem.sharedPlaquetteEnergyActionOscillation
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (finite_lattice_plaquetteEnergyMax_nonneg L)

/-- The active local action-difference oscillation is controlled by the exact
active shared-plaquette multiplicity rather than the total plaquette count. -/
theorem finite_lattice_activeLocalActionDifferenceOscillationBound_sharedEnergy
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.ActiveLocalActionDifferenceOscillationBound
      (L.sharedPlaquetteEnergyActionOscillation hEdge) := by
  intro target source A g hActive u v
  have hCardNat :=
    finite_lattice_sharedPlaquettes_card_le_canonicalActiveMultiplicity
      L hEdge target source hActive
  have hCard :
      ((L.sharedPlaquettes target source).card : ℝ) ≤
        (L.canonicalActiveSharedPlaquetteMultiplicity hEdge : ℝ) := by
    exact_mod_cast hCardNat
  have hNonneg := finite_lattice_plaquetteEnergyMax_nonneg L
  have huRaw :=
    finite_lattice_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul_energyMax
      L A target source u g
  have hvRaw :=
    finite_lattice_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul_energyMax
      L A target source v g
  have hScale :
      ((L.sharedPlaquettes target source).card : ℝ) *
          L.plaquetteEnergyMax ≤
        (L.canonicalActiveSharedPlaquetteMultiplicity hEdge : ℝ) *
          L.plaquetteEnergyMax :=
    mul_le_mul_of_nonneg_right hCard hNonneg
  have hu := le_trans huRaw hScale
  have hv := le_trans hvRaw hScale
  have huBounds := abs_le.mp hu
  have hvBounds := abs_le.mp hv
  unfold FiniteLatticeWilsonSystem.sharedPlaquetteEnergyActionOscillation
  linarith

/-- Refined conditional likelihood-ratio control using only the exact active
shared-plaquette multiplicity. -/
theorem finite_lattice_activeConditionalExpRatioBound_sharedPlaquetteEnergy
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.ActiveConditionalExpRatioBound
      (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge) :=
  finite_lattice_activeConditionalExpRatioBound_of_localActionOscillation
    L (L.sharedPlaquetteEnergyActionOscillation hEdge)
      (finite_lattice_sharedPlaquetteEnergyActionOscillation_nonneg L hEdge)
      (finite_lattice_activeLocalActionDifferenceOscillationBound_sharedEnergy
        L hEdge)

/-- The exact active influence maximum is bounded by the refined shared-energy
normalized-exponential majorant. -/
theorem finite_lattice_canonicalActivePlaquetteInfluenceBound_le_sharedEnergyExpRatio
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalActivePlaquetteInfluenceBound hEdge ≤
      (Real.exp
          (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge) - 1) /
        (Real.exp
          (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge) + 1) :=
  finite_lattice_canonicalActivePlaquetteInfluenceBound_le_expRatioBound
    L hEdge
      (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge)
      (mul_nonneg L.beta_nonneg
        (finite_lattice_sharedPlaquetteEnergyActionOscillation_nonneg L hEdge))
      (finite_lattice_activeConditionalExpRatioBound_sharedPlaquetteEnergy
        L hEdge)

/-- The refined shared-plaquette scalar threshold implies strict canonical
Dobrushin contraction. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_sharedPlaquetteEnergy
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hDegreePos : 0 < L.canonicalActivePlaquetteDegree hEdge)
    (hThreshold :
      (Real.exp
          (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge) - 1) /
          (Real.exp
            (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge) + 1) <
        (L.canonicalActivePlaquetteDegree hEdge : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  finite_lattice_canonicalDobrushinCoefficient_lt_one_of_activeConditionalExpRatio
    L hEdge hDegreePos
      (L.beta * L.sharedPlaquetteEnergyActionOscillation hEdge)
      (mul_nonneg L.beta_nonneg
        (finite_lattice_sharedPlaquetteEnergyActionOscillation_nonneg L hEdge))
      (finite_lattice_activeConditionalExpRatioBound_sharedPlaquetteEnergy
        L hEdge)
      hThreshold

/-- Family-level refined concrete input using the exact active shared-plaquette
multiplicity at each scale. -/
structure FiniteWilsonSharedPlaquetteEnergyFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  activeDegree_pos : ∀ i : W.index,
    0 < (W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i)
  sharedEnergyThreshold : ∀ i : W.index,
    (Real.exp
        ((W.system i).beta *
          (W.system i).sharedPlaquetteEnergyActionOscillation
            (edgeCard_pos i)) - 1) /
        (Real.exp
          ((W.system i).beta *
            (W.system i).sharedPlaquetteEnergyActionOscillation
              (edgeCard_pos i)) + 1) <
      ((W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i) : ℝ)⁻¹

/-- Convert refined shared-plaquette energy data into the action-oscillation
family package. -/
noncomputable def
    FiniteWilsonSharedPlaquetteEnergyFamilyData.toActionOscillationFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonSharedPlaquetteEnergyFamilyData W) :
    FiniteWilsonActiveLocalActionOscillationFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    activeDegree_pos := D.activeDegree_pos
    actionOscillation := fun i =>
      (W.system i).sharedPlaquetteEnergyActionOscillation (D.edgeCard_pos i)
    actionOscillation_nonneg := fun i =>
      finite_lattice_sharedPlaquetteEnergyActionOscillation_nonneg
        (W.system i) (D.edgeCard_pos i)
    activeLocalActionOscillationBound := fun i =>
      finite_lattice_activeLocalActionDifferenceOscillationBound_sharedEnergy
        (W.system i) (D.edgeCard_pos i)
    normalizedExpTV_lt_inv_activeDegree := D.sharedEnergyThreshold }

/-- Refined shared-plaquette energy data generate normalized Hamiltonian gap
data at every scale. -/
noncomputable def
    FiniteWilsonSharedPlaquetteEnergyFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonSharedPlaquetteEnergyFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.toActionOscillationFamilyData.hamiltonianGapData i

/-- The refined shared-energy threshold gives normalized Hamiltonian exact-gap
coercivity on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_shared_plaquette_energy_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonSharedPlaquetteEnergyFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.toActionOscillationFamilyData.toConditionalExpRatioFamilyData.toReciprocalInfluenceFamilyData.toProductFamilyData.rayleighFamilyData.atScale i)
          x) x :=
  finite_wilson_active_local_action_oscillation_family_hamiltonian_gap
    W D.toActionOscillationFamilyData i x hx

/-- Every excitation-sector eigenvalue generated by the refined shared-energy
criterion is bounded below by the public exact gap. -/
theorem finite_wilson_shared_plaquette_energy_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonSharedPlaquetteEnergyFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_active_local_action_oscillation_family_restricted_eigenvalues_ge_exactGap
    W D.toActionOscillationFamilyData i j

end

end MathlibAnalytic
end MGAP4D
