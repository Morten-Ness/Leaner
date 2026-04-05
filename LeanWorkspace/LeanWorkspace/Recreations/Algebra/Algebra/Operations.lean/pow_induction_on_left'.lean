import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem pow_induction_on_left' {C : ∀ (n : ℕ) (x), x ∈ M ^ n → Prop}
    (algebraMap : ∀ r : R, C 0 (algebraMap _ _ r) (Submodule.algebraMap_mem r))
    (add : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
    (mem_mul : ∀ m (hm : m ∈ M), ∀ (i x hx), C i x hx → C i.succ (m * x)
      ((Submodule.pow_succ' M i).symm ▸ (Submodule.mul_mem_mul hm hx)))
    {n : ℕ} {x : A}
    (hx : x ∈ M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [Submodule.pow_zero] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [Submodule.pow_succ']
    exact fun hx ↦ Submodule.mul_induction_on' (fun m hm x ih => mem_mul _ hm _ _ _ (n_ih ih))
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

