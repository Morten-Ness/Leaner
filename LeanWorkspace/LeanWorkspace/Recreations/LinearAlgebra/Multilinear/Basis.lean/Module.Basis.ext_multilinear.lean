import Mathlib

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

theorem Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι → Type*}
    (e : ∀ i, Basis (ιM i) R (M i))
    (h : ∀ v : (i : ι) → ιM i, (f fun i ↦ e i (v i)) = g fun i ↦ e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i ↦ (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

