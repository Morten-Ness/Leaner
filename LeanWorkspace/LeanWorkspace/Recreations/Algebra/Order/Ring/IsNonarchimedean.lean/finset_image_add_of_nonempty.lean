import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

omit [Semiring R] in
theorem finset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α → R}
    (hna : IsNonarchimedean f) (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b ∈ t, f (t.sum g) ≤ f (g b) := by
  apply IsNonarchimedean.multiset_image_add_of_nonempty hna
  simp_all [Finset.nonempty_iff_ne_empty]

