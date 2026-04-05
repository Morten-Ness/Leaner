import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

variable {B : Type u₄} [Semiring B] [Algebra S B]

theorem eq_liftAlgHom_comp_mkAlgHom {s : A → A → Prop} (f : RingQuot s →ₐ[S] B) :
    f = liftAlgHom S ⟨f.comp (mkAlgHom S s), fun _ _ h ↦ congr_arg f (RingQuot.mkAlgHom_rel S h)⟩ := RingQuot.liftAlgHom_unique S (f.comp (mkAlgHom S s)) (fun _ _ h ↦ congr_arg (⇑f) (RingQuot.mkAlgHom_rel S h)) f rfl

