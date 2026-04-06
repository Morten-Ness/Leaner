FAIL
import Mathlib

universe uι u v

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem pow_induction_on_left {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ m ∈ M, ∀ (x), C x → C (m * x)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x := by
  induction n generalizing x with
  | zero =>
      rw [Submodule.pow_zero] at hx
      rcases hx with ⟨r, rfl⟩
      exact hr r
  | succ n ih =>
      rw [Submodule.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?hm ?h0 ?ha
      · intro y hy z hz
        exact hmul y hy z (ih hz)
      · exact hr 0
      · intro a b ha hb
        exact hadd a b ha hb
