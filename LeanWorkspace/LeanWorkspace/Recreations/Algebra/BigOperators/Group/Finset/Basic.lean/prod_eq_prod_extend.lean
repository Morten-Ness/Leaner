import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_prod_extend (f : s → M) : ∏ x, f x = ∏ x ∈ s, Subtype.val.extend f 1 x := by
  rw [univ_eq_attach, ← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

