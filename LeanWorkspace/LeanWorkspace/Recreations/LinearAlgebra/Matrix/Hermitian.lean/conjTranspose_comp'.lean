import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem conjTranspose_comp' {I J K : Type*} (M : Matrix I J (Matrix K K α)) :
    (comp I J K K α M)ᴴ = comp J I K K α Mᴴ := rfl

