import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem conjTranspose_comp {I J K L : Type*} (M : Matrix I J (Matrix K L α)) :
    (comp I J K L α M)ᴴ = comp J I L K α (Mᵀ.map (·ᴴ)) := rfl

