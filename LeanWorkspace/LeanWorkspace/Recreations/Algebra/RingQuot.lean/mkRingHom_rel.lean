import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem mkRingHom_rel {r : R → R → Prop} {x y : R} (w : r x y) : mkRingHom r x = mkRingHom r y := by
  simp [mkRingHom_def, Quot.sound (Rel.of w)]

