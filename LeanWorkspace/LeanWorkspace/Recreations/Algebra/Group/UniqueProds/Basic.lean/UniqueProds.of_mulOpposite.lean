import Mathlib

variable (G : Type u) (H : Type v) [Mul G] [Mul H]

theorem of_mulOpposite (h : UniqueProds Gᵐᵒᵖ) : UniqueProds G where
  uniqueMul_of_nonempty hA hB := let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    let ⟨y, yB, x, xA, hxy⟩ := h.uniqueMul_of_nonempty (hB.map (f := f)) (hA.map (f := f))
    ⟨unop x, (mem_map' _).mp xA, unop y, (mem_map' _).mp yB, UniqueMul.of_mulOpposite hxy⟩

