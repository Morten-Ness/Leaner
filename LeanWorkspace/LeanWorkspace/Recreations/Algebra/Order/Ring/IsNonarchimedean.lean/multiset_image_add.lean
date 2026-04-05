import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem multiset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f) (g : β → α)
    (s : Multiset β) : ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := IsNonarchimedean.multiset_image_add_of_nonempty (s := a ::ₘ s)
      hna g Multiset.cons_ne_zero
    exact ⟨b, fun _ ↦ hb1, hb2⟩

