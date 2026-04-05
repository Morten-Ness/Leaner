import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem pow_induction_on_left {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ m ∈ M, ∀ (x), C x → C (m * x)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x := Submodule.pow_induction_on_left' M (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _m hm _i _x _hx => hmul _ hm _) hx

