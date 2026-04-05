import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b := ⟨ContravariantClass.elim _, CovariantClass.elim _⟩

