import Mathlib

section

open scoped Finset

variable {ι κ M N R α : Type*}

theorem Finset.prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι → ∀ a, M a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a := map_prod (Pi.evalMonoidHom M a) _ _

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

theorem Finset.prod_fn {α : Type*} {M : α → Type*} {ι} [∀ a, CommMonoid (M a)] (s : Finset ι)
    (g : ι → ∀ a, M a) : ∏ c ∈ s, g c = fun a ↦ ∏ c ∈ s, g c a := funext fun _ ↦ Finset.prod_apply _ _ _

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {M : I → Type*}

variable [∀ i, CommMonoid (M i)]

theorem MonoidHom.functions_ext' [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i, g.comp (MonoidHom.mulSingle M i) = h.comp (MonoidHom.mulSingle M i)) : g = h := g.functions_ext N h fun i => DFunLike.congr_fun (H i)

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {M : I → Type*}

variable [∀ i, CommMonoid (M i)]

theorem MonoidHom.functions_ext [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k, map_prod, map_prod]
  simp only [H]

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem Pi.mulSingle_induction [∀ i, CommMonoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (one : p 1) (mul : ∀ f g, p f → p g → p (f * g))
    (mulSingle : ∀ i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem Pi.single_induction [∀ i, AddCommMonoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (single : ∀ i m, p (Pi.single i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {R : I → Type*}

variable [∀ i, NonAssocSemiring (R i)]

theorem RingHom.functions_ext [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (∀ i, R i) →+* S)
    (H : ∀ (i : I) (x : R i), g (single i x) = h (single i x)) : g = h := RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (∀ i, R i) →+ S) h H

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s := fun t ht => by simp [funext fun i ↦ h i ht]

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  convert eqOn_finsetProd h v <;> simp

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

theorem list_prod_apply {α : Type*} {M : α → Type*} [∀ a, Monoid (M a)] (a : α)
    (l : List (∀ a, M a)) : l.prod a = (l.map fun f : ∀ a, M a ↦ f a).prod := map_list_prod (evalMonoidHom M a) _

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

theorem multiset_prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Multiset (∀ a, M a)) : s.prod a = (s.map fun f : ∀ a, M a ↦ f a).prod := (evalMonoidHom M a).map_multiset_prod _

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

theorem pi_eq_sum_univ' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • Pi.single (M := fun _ ↦ R) i 1 := by
  convert pi_eq_sum_univ x
  aesop

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommSemiring R]

theorem prod_indicator (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) :
    ∏ i ∈ s, (f i).indicator (g i) = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) := by
  ext a; simpa using prod_indicator_apply ..

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommSemiring R]

theorem prod_indicator_apply (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) (j : κ) :
    ∏ i ∈ s, (f i).indicator (g i) j = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) j := by
  rw [Set.indicator]
  split_ifs with hj
  · rw [Finset.prod_apply]
    congr! 1 with i hi
    simp only [Set.mem_iInter] at hj
    exact Set.indicator_of_mem (hj _ hi) _
  · obtain ⟨i, hi, hj⟩ := by simpa using hj
    exact Finset.prod_eq_zero hi <| Set.indicator_of_notMem hj _

end

section

open scoped Finset

variable {ι κ M N R α : Type*}

theorem prod_mk_prod [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι → M) (g : ι → N) :
    (∏ x ∈ s, f x, ∏ x ∈ s, g x) = ∏ x ∈ s, (f x, g x) := haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

end
