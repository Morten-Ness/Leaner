import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [CommRing α] [StarRing α]

theorem isHermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A] :
    A⁻¹.IsHermitian ↔ A.IsHermitian := ⟨fun h => by rw [← inv_inv_of_invertible A]; exact Matrix.IsHermitian.inv h, Matrix.IsHermitian.inv⟩

