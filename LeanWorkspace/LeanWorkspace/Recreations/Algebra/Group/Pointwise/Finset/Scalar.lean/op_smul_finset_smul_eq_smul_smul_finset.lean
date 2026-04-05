import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, Finset.mem_smul_finset, h]

