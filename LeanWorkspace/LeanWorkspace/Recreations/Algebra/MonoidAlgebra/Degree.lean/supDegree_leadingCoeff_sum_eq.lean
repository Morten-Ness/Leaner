import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

theorem supDegree_leadingCoeff_sum_eq
    (hi : i ∈ s) (hmax : ∀ j ∈ s, j ≠ i → (f j).supDegree D < (f i).supDegree D) :
    (∑ j ∈ s, f j).supDegree D = (f i).supDegree D ∧
    (∑ j ∈ s, f j).leadingCoeff D = (f i).leadingCoeff D := by
  classical
  rw [← s.add_sum_erase _ hi]
  by_cases! hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨AddMonoidAlgebra.supDegree_add_eq_left this, AddMonoidAlgebra.leadingCoeff_add_eq_left this⟩
  refine AddMonoidAlgebra.supDegree_sum_lt ?_ (fun j hj => ?_)
  · exact hs
  · rw [Finset.mem_erase] at hj; exact hmax j hj.2 hj.1

