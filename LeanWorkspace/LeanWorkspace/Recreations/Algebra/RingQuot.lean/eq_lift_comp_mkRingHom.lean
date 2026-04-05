import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

theorem eq_lift_comp_mkRingHom {r : R → R → Prop} (f : RingQuot r →+* T) :
    f = lift ⟨f.comp (mkRingHom r), fun _ _ h ↦ congr_arg f (RingQuot.mkRingHom_rel h)⟩ := RingQuot.lift_unique (f.comp (mkRingHom r)) (fun _ _ h ↦ congr_arg (⇑f) (RingQuot.mkRingHom_rel h)) f rfl

