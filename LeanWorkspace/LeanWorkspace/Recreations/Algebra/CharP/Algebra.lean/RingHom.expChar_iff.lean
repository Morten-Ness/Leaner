import Mathlib

variable {R A : Type*}

theorem RingHom.expChar_iff [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) : ExpChar R p ↔ ExpChar A p := ⟨fun _ ↦ expChar_of_injective_ringHom H p, fun _ ↦ f.expChar H p⟩

