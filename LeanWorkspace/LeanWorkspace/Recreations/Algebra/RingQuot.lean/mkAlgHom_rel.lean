import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

theorem mkAlgHom_rel {s : A → A → Prop} {x y : A} (w : s x y) :
    mkAlgHom S s x = mkAlgHom S s y := by
  simp [mkAlgHom_def, mkRingHom_def, Quot.sound (Rel.of w)]

