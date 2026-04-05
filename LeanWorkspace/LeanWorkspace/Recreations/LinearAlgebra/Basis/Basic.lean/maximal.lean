import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem maximal [Nontrivial R] (b : Module.Basis ι R M) : Module.Basis.linearIndependent b.Maximal := fun w hi h => by
  -- If `w` is strictly bigger than `Set.range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ Set.range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the Set.range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  simp_rw [Finsupp.linearCombination_apply] at e
  change ((b.repr x).sum fun (i : ι) (a : R) ↦ a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
  rw [← Finsupp.sum_embDomain (f := u) (g := fun x r ↦ r • (x : M)),
      ← Finsupp.linearCombination_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine hi.linearCombination_ne_of_notMem_support _ ?_ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [u, Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
  apply q ⟨j, W⟩

