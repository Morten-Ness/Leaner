import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  nontriviality R
  rw [Polynomial.natDegree_multiset_prod']
  simp_rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction

