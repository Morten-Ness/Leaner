import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

theorem range_smul_range {ι κ : Type*} [SMul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ ↦ b p.1 • c p.2 := image2_range ..

