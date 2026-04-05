import Mathlib

variable {ι α β M N P G : Type*}

theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.prod = -1) : (-1 : ℤ) ∈ l := by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (List.prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁

