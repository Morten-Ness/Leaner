import Mathlib

variable (G : Type u) (H : Type v) [Mul G] [Mul H]

theorem of_mulOpposite (h : TwoUniqueProds Gᵐᵒᵖ) : TwoUniqueProds G where
  uniqueMul_of_one_lt_card hc := by
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    rw [← card_map f, ← card_map f, mul_comm] at hc
    obtain ⟨p1, h1, p2, h2, hne, hu1, hu2⟩ := h.uniqueMul_of_one_lt_card hc
    simp_rw [mem_product] at h1 h2 ⊢
    refine ⟨(_, _), ⟨?_, ?_⟩, (_, _), ⟨?_, ?_⟩, ?_, UniqueMul.of_mulOpposite hu1, UniqueMul.of_mulOpposite hu2⟩
    pick_goal 5
    · contrapose! hne; rw [Prod.ext_iff] at hne ⊢
      exact ⟨unop_injective hne.2, unop_injective hne.1⟩
    all_goals apply (mem_map' f).mp
    exacts [h1.2, h1.1, h2.2, h2.1]

