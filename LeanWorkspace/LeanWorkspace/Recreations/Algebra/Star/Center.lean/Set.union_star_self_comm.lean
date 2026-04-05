import Mathlib

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

theorem Set.union_star_self_comm (hcomm : ∀ x ∈ s, ∀ y ∈ s, y * x = x * y)
    (hcomm_star : ∀ x ∈ s, ∀ y ∈ s, y * star x = star x * y) :
    ∀ x ∈ s ∪ star s, ∀ y ∈ s ∪ star s, y * x = x * y := by
  change s ∪ star s ⊆ (s ∪ star s).centralizer
  simp_rw [centralizer_union, ← star_centralizer, union_subset_iff, subset_inter_iff,
    star_subset_star, star_subset]
  exact ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩

