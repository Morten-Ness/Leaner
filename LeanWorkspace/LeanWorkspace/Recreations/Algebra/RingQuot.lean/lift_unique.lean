import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

theorem lift_unique (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y)
    (g : RingQuot r →+* T) (h : g.comp (mkRingHom r) = f) : g = lift ⟨f, w⟩ := by
  ext
  simp [h]

