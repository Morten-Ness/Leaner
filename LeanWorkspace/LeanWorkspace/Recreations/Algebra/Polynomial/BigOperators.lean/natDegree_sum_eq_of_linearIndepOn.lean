import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

theorem natDegree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι → R[X]}
    {v : ι → A} (h : LinearIndepOn R v s) :
    (∑ i ∈ s, v i • (f i).map (algebraMap R A)).natDegree = s.sup (fun i ↦ (f i).natDegree) := by
  apply le_antisymm
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (natDegree_smul_le _ _).trans <|
      natDegree_map_le.trans <| Finset.le_sup (f := fun i ↦ (f i).natDegree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    apply le_natDegree_of_ne_zero
    rw [finset_sum_coeff]
    conv in (fun _ ↦ _) =>
      ext
      rw [coeff_smul, smul_eq_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

