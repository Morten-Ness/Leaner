import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable (G) [InvolutiveInv G]

theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G := rfl

