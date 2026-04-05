import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

variable {_ : NonAssocSemiring γ}

theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) :
    (hnp.comp hmn : α → γ) x = hnp (hmn x) := rfl

