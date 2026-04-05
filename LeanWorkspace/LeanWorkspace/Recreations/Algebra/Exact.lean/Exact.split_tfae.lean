import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      ∃ l, g ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

