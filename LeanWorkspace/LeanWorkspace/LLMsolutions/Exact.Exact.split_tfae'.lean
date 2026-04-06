FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Exact.split_tfae' (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ ∃ l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  constructor
  · intro h1
    rcases h1 with ⟨hf, l, hl⟩
    have hg : Function.Surjective g := by
      intro p
      refine ⟨l p, ?_⟩
      simpa using congrArg (fun u => u p) hl
    rcases (h.split_tfae hf hg).out 0 (by simp) with h01
    exact ⟨hg, h01 ⟨l, hl⟩⟩
  · intro h2
    rcases h2 with ⟨hg, l, hl⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have := congrArg l hxy
      simpa using this
    rcases (h.split_tfae hf hg).out 1 (by simp) with h12
    exact h12 ⟨l, hl⟩
  · intro h3
    rcases h3 with ⟨e, hf_eq, hg_eq⟩
    have hf : Function.Injective f := by
      rw [hf_eq]
      exact (e.symm.injective.comp <| (LinearMap.inl R M P).injective)
    have hg : Function.Surjective g := by
      rw [hg_eq]
      exact (LinearMap.snd R M P).surjective.comp e.surjective
    rcases (h.split_tfae hf hg).out 2 (by simp) with h20
    exact h20 ⟨e, hf_eq, hg_eq⟩
  · intro h1
    rcases h1 with ⟨hf, l, hl⟩
    have hg : Function.Surjective g := by
      intro p
      refine ⟨l p, ?_⟩
      simpa using congrArg (fun u => u p) hl
    rcases (h.split_tfae hf hg).mp with ⟨_, hrest⟩
    rcases hrest.mp with ⟨_, h23⟩
    exact h23.mp
  · intro h2
    rcases h2 with ⟨hg, l, hl⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have := congrArg l hxy
      simpa using this
    rcases (h.split_tfae hf hg).mp with ⟨h12, _⟩
    exact h12.mpr
  · intro h3
    rcases h3 with ⟨e, hf_eq, hg_eq⟩
    have hf : Function.Injective f := by
      rw [hf_eq]
      exact (e.symm.injective.comp <| (LinearMap.inl R M P).injective)
    have hg : Function.Surjective g := by
      rw [hg_eq]
      exact (LinearMap.snd R M P).surjective.comp e.surjective
    rcases (h.split_tfae hf hg).mp with ⟨h12, hrest⟩
    rcases hrest.mp with ⟨h23, _⟩
    exact h23.mpr ⟨e, hf_eq, hg_eq⟩
