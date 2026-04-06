FAIL
import Mathlib

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem pow_induction_on_right {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ x, C x → ∀ m ∈ M, C (x * m)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x := by
  let N : Submodule R A :=
    { carrier := {x : A | C x}
      zero_mem' := by simpa using hr (0 : R)
      add_mem' := by
        intro x y hx hy
        exact hadd x y hx hy
      smul_mem' := by
        intro r x hx
        simpa [Algebra.smul_def, mul_comm] using hmul x hx ((algebraMap R A) r)
          (show (algebraMap R A) r ∈ M by simpa using M.smul_mem r (show (1 : A) ∈ M by simpa using M.one_mem)) }
  have hM : M ≤ N := by
    intro m hm
    simpa [one_mul] using hmul 1 (by simpa using hr (1 : R)) m hm
  have hpow : M ^ n ≤ N := by
    exact le_trans (Submodule.pow_le_pow_right hM n) (by simpa using le_rfl : N ^ n ≤ N)
  exact hpow hx
