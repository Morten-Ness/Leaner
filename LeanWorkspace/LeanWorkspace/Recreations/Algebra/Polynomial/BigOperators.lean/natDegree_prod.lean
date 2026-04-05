import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_prod (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  nontriviality R
  apply Polynomial.natDegree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]

