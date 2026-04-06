FAIL
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
  classical
  rcases h.split hf hg with ⟨s, hs, r, hr, e, rfl⟩
  have h0 : (∃ l, g ∘ₗ l = LinearMap.id) := ⟨s, hs⟩
  have h1 : (∃ l, l ∘ₗ f = LinearMap.id) := ⟨r, hr⟩
  have h2 : (∃ e' : N ≃ₗ[R] M × P,
      f = e'.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e') := by
    refine ⟨e, ?_, ?_⟩
    · ext m
      simp
    · ext n
      simp
  refine List.tfae_of_cycle ?_
  intro i hi
  fin_cases i
  · simpa using (show h0 → h1 from fun _ => h1)
  · simpa using (show h1 → h2 from fun _ => h2)
  · simpa using (show h2 → h0 from fun _ => h0)
