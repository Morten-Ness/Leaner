import Mathlib

variable {ι α β M N P G : Type*}

theorem Sublist.prod_dvd_prod [CommMonoid M] {l₁ l₂ : List M} (h : l₁ <+ l₂) :
    l₁.prod ∣ l₂.prod := by
  obtain ⟨l, hl⟩ := h.exists_perm_append
  rw [hl.prod_eq, prod_append]
  exact dvd_mul_right _ _

