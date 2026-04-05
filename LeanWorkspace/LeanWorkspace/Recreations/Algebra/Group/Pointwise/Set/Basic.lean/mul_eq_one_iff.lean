import Mathlib

variable {F α β γ : Type*}

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hst : (s * t).Nonempty := h.symm.subst Set.one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun {a b} ha hb =>
      h.subset <| mem_image2_of_mem ha hb
    refine ⟨a, b, ?_, ?_, H ha hb⟩ <;> refine eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => ?_⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [Set.singleton_mul_singleton, h, Set.singleton_one]

