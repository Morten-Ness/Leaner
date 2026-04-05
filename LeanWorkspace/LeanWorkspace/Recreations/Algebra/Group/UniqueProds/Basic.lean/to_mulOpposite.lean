import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem to_mulOpposite (h : UniqueMul A B a0 b0) :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) := UniqueMul.of_mulOpposite (by simp_rw [map_map]; exact (UniqueMul.mulHom_map_iff _ fun _ _ ↦ by rfl).mpr h)

