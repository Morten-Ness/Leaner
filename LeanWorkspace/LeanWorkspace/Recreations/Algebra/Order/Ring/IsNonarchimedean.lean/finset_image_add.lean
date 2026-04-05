import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem finset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  have h1 : t.Nonempty ↔ t.val ≠ 0 := by simp [Finset.nonempty_iff_ne_empty]
  rw [h1]
  exact IsNonarchimedean.multiset_image_add hna g t.val

