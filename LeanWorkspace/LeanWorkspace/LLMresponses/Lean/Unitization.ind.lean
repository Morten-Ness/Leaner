FAIL
import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (inl_add_inr : ∀ (r : R) (a : A), P (Unitization.inl r + (a : Unitization R A))) (x) : P x := by
  rcases x with ⟨r, a⟩
  simpa [Unitization.inl, Unitization.instAdd, Add.add, Unitization.coeToProd] using inl_add_inr r a
