import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (g : S →+* T) (f : R →+* S)

theorem mem_rangeS_self (f : R →+* S) (x : R) : f x ∈ f.rangeS := RingHom.mem_rangeS.mpr ⟨x, rfl⟩

