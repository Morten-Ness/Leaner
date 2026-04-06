FAIL
import Mathlib

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem pow_induction_on_right' {C : ∀ (n : ℕ) (x), x ∈ M ^ n → Prop}
    (algebraMap : ∀ r : R, C 0 (algebraMap _ _ r) (Submodule.algebraMap_mem r))
    (add : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
    (mul_mem :
      ∀ i x hx, C i x hx →
        ∀ m (hm : m ∈ M), C i.succ (x * m) (Submodule.mul_mem_mul hx hm))
    {n : ℕ} {x : A} (hx : x ∈ M ^ n) : C n x hx := by
  revert x
  induction n with
  | zero =>
      intro x hx
      rw [pow_zero] at hx
      rcases hx with ⟨r, rfl⟩
      simpa using algebraMap r
  | succ n ih =>
      intro x hx
      rw [Submodule.pow_succ] at hx
      exact Submodule.mul_induction_on hx
        (fun y z hy hz =>
          add y z (n + 1) hy hz)
        (fun y hy m hm =>
          mul_mem n y hy (ih hy) m hm)
