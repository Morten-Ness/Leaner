import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [Semiring R] [Semiring S] [AddCommMonoid A]

variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) := by
  rw [Submodule.span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)

