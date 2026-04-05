import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem ringQuot_ext [NonAssocSemiring T] {r : R → R → Prop} (f g : RingQuot r →+* T)
    (w : f.comp (mkRingHom r) = g.comp (mkRingHom r)) : f = g := by
  ext x
  rcases RingQuot.mkRingHom_surjective r x with ⟨x, rfl⟩
  exact (RingHom.congr_fun w x :)

