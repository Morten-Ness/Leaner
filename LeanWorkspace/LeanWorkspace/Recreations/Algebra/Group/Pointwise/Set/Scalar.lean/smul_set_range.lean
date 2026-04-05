import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

theorem smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    a • range f = range fun i ↦ a • f i := (range_comp ..).symm

