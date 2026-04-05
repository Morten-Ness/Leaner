import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

theorem degree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι → R[X]}
    {v : ι → A} (h : LinearIndepOn R v s) :
    (∑ i ∈ s, v i • (f i).map (algebraMap R A)).degree = s.sup (fun i ↦ (f i).degree) := by
  apply le_antisymm
  · exact (degree_sum_le s _).trans <| Finset.sup_le fun i hi ↦ (degree_smul_le _ _).trans <|
      degree_map_le.trans <| Finset.le_sup (f := fun i ↦ (f i).degree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    rw [degree_eq_natDegree hf]
    apply le_degree_of_ne_zero
    rw [finset_sum_coeff]
    conv in (fun _ ↦ _) =>
      ext
      rw [coeff_smul, smul_eq_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

-- Note: Proof duplicated from the `degree` version, since the statements don't
-- trivially follow from each other.

