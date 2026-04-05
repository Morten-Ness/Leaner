import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

include f in
theorem domain_nontrivial [Nontrivial β] : Nontrivial α := ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, RingHom.map_zero]) RingHom.map_one_ne_zero f⟩⟩

