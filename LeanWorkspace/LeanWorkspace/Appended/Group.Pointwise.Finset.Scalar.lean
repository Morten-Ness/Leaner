import Mathlib

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [VSub α β] {s t : Set β}

theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, mem_image]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, Finset.mem_smul_finset, h]

end
