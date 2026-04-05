import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

theorem supDegree_sum_lt (hs : s.Nonempty) {b : B}
    (h : ∀ i ∈ s, (f i).supDegree D < b) : (∑ i ∈ s, f i).supDegree D < b := by
  refine AddMonoidAlgebra.supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

