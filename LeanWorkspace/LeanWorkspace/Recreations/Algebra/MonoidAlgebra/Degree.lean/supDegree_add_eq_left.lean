import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

set_option backward.isDefEq.respectTransparency false in
theorem supDegree_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).supDegree D = p.supDegree D := by
  apply (AddMonoidAlgebra.supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := AddMonoidAlgebra.exists_supDegree_mem_support D (AddMonoidAlgebra.ne_zero_of_not_supDegree_le h.not_ge)
  rw [he] at h ⊢
  apply Finset.le_sup
  rw [mem_support_iff, add_apply, AddMonoidAlgebra.apply_eq_zero_of_not_le_supDegree h.not_ge, add_zero]
  exact mem_support_iff.mp ha

