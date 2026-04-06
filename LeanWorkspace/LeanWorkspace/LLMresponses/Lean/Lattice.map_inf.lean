import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_inf (f : A →ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha.1, rfl⟩, ⟨a, ha.2, rfl⟩⟩
  · rintro ⟨hxS, hxT⟩
    rcases hxS with ⟨a, haS, hax⟩
    rcases hxT with ⟨b, hbT, hbx⟩
    have hfab : f a = f b := by
      calc
        f a = x := hax
        _ = f b := hbx.symm
    have hab : a = b := hf hfab
    subst a
    exact ⟨b, ⟨haS, hbT⟩, hbx⟩
