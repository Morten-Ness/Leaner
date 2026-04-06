import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  rcases Multiset.le_iff_exists_add.mp h with ⟨u, rfl⟩
  refine ⟨u.prod, ?_⟩
  simp [Multiset.prod_add]
