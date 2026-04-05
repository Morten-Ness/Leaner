import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem of_mulOpposite
    (h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) :
    UniqueMul A B a0 b0 := fun a b aA bB ab ↦ by
  simpa [and_comm] using h (mem_map_of_mem _ bB) (mem_map_of_mem _ aA) (congr_arg op ab)

