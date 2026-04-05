import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).prod.roots = s := by
  rw [Polynomial.roots_multiset_prod, Multiset.bind_map]
  · simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h

