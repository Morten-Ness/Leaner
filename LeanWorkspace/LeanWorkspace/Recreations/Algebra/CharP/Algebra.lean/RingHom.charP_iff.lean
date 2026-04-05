import Mathlib

variable {R A : Type*}

theorem RingHom.charP_iff [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (H : Function.Injective f) (p : ℕ) : CharP R p ↔ CharP A p := ⟨fun _ ↦ charP_of_injective_ringHom H p, fun _ ↦ f.charP H p⟩

