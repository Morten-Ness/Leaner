import Mathlib

theorem CanonicallyOrderedAdd.multiset_prod_pos {R : Type*}
    [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R]
    {m : Multiset R} : 0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos

