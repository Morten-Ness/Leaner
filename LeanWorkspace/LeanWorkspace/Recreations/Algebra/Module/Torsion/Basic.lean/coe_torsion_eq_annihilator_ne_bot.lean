import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable [NoZeroDivisors R] [Nontrivial R]

theorem coe_torsion_eq_annihilator_ne_bot :
    (torsion R M : Set M) = { x : M | (R ∙ x).annihilator ≠ ⊥ } := by
  ext x; simp_rw [Submodule.ne_bot_iff, mem_annihilator, mem_span_singleton]
  exact
    ⟨fun ⟨a, hax⟩ =>
      ⟨a, fun _ ⟨b, hb⟩ => by rw [← hb, smul_comm, ← Submonoid.smul_def, hax, smul_zero],
        nonZeroDivisors.coe_ne_zero _⟩,
      fun ⟨a, hax, ha⟩ => ⟨⟨_, mem_nonZeroDivisors_of_ne_zero ha⟩, hax x ⟨1, one_smul _ _⟩⟩⟩

