import Mathlib

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem _root_.Submodule.eq_top_iff_forall_basis_mem {p : Submodule R M} :
    p = ⊤ ↔ ∀ i, b i ∈ p := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  replace h : Set.range b ⊆ p := by rintro - ⟨i, rfl⟩; exact h i
  simpa using span_mono (R := R) h

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem basis_singleton_iff {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsTorsionFree R M] (ι : Type*) [Unique ι] :
    Nonempty (Module.Basis ι R M) ↔ ∃ x ≠ 0, ∀ y : M, ∃ r : R, r • x = y := by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, Module.Basis.linearIndependent Module.Basis.ne_zero b _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using Module.Basis.span_eq b
  · rintro ⟨x, nz, w⟩
    refine ⟨ofRepr <| LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single default (w y).choose
        left_inv := fun f => Finsupp.unique_ext ?_
        right_inv := fun y => ?_
        map_add' := fun y z => ?_
        map_smul' := fun c y => ?_ }⟩
    · simp [Finsupp.add_apply, add_smul]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_assoc]
    · refine smul_left_injective _ nz ?_
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

theorem card_fintype [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι] (b : Basis ι R M)
    [Fintype R] [Fintype M] :
    card M = card R ^ card ι := by
  classical
    calc
      card M = card (ι → R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := by simp

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem index_nonempty (b : Module.Basis ι R M) [Nontrivial M] : Nonempty ι := by
  obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem linearIndependent : LinearIndependent R b := fun x y hxy => by
    rw [← b.repr_linearCombination x, hxy, b.repr_linearCombination y]

protected lemma linearIndepOn (s : Set ι) : LinearIndepOn R b s :=
  b.linearIndependent.linearIndepOn s

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem linearIndependent_coord {R : Type*} [CommSemiring R] [Module R M] (b : Module.Basis ι R M) :
    LinearIndependent R b.coord := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj ↦ ?_
  simpa [hj, Finsupp.single_apply] using congr($h (b j))

end

section

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

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem mem_span (x : M) : x ∈ span R (Set.range b) := span_mono (image_subset_range _ _) (Module.Basis.mem_span_repr_support b x)

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem mem_span_image {m : M} {s : Set ι} : m ∈ span R (b '' s) ↔ ↑(b.repr m).support ⊆ s := ⟨Module.Basis.repr_support_subset_of_mem_span _ _, fun h ↦
    span_mono (Set.image_mono h) (Module.Basis.mem_span_repr_support b _)⟩

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem mem_span_repr_support (m : M) : m ∈ span R (b '' (b.repr m).support) := (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_apply (i : ι) : Module.Basis.mk hli hsp i = v i := show Finsupp.linearCombination _ v _ = v i by simp

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Module.Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, Module.Basis.mk_coord_apply_eq i]
  · simp only [h, if_false, Module.Basis.mk_coord_apply_ne h]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_coord_apply_eq (i : ι) : (Module.Basis.mk hli hsp).coord i (v i) = 1 := show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Module.Basis.mk hli hsp).coord i (v j) = 0 := show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 := Module.Basis.linearIndependent b.ne_zero i

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem repr_range : LinearMap.range (b.repr : M →ₗ[R] ι →₀ R) = Finsupp.supported R R Set.univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem repr_support_subset_of_mem_span (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s := by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem self_mem_span_image [Nontrivial R] {i : ι} {s : Set ι} :
    b i ∈ span R (b '' s) ↔ i ∈ s := by
  simp [Module.Basis.mem_span_image, Finsupp.support_single_ne_zero]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Module.Basis.singleton ι R i = 1 := apply_eq_iff.mpr (by simp [Module.Basis.singleton])

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) :
    (Module.Basis.singleton ι R).repr x i = x := by simp [Module.Basis.singleton, Unique.eq_default i]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem smul_eq_zero [IsDomain R] (b : Module.Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 := by have := b.isTorsionFree; exact smul_eq_zero

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v)

theorem span_apply (i : ι) :
    Module.Basis.span hli i = ⟨v i, Submodule.subset_span <| mem_range_self _⟩ := by
  ext
  exact congr_arg ((↑) : span R (Set.range v) → M) <| Module.Basis.mk_apply _ _ _

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem span_eq : span R (Set.range b) = ⊤ := eq_top_iff.mpr fun x _ => Module.Basis.mem_span b x

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v)

theorem span_neg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {v : ι → M} (hli : LinearIndependent R v)
    (h : span R (Set.range v) = span R (Set.range (-v)) := by simp [← neg_range']) :
    Module.Basis.span hli.neg = ((Module.Basis.span hli).map <| (LinearEquiv.neg _).trans (.ofEq _ _ h)) := by
  ext; simp

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (hli : LinearIndependent R v)

theorem span_repr_eq_single (i : ι)
    (hi : v i ∈ span R (Set.range v) := subset_span <| mem_range_self i) :
    (Module.Basis.span hli).repr ⟨v i, hi⟩ = single i 1 := by
  rw [← LinearEquiv.eq_symm_apply]
  simp [Module.Basis.span]

end
