import Mathlib

variable {F α β γ : Type*}

theorem image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s := image_comm

