import Mathlib

variable {F α β γ : Type*}

variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

theorem op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext; simp [mem_smul, mem_smul_set, h]

