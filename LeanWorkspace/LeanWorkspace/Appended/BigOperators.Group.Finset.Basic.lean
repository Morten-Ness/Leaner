import Mathlib

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem exists_ne_one_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  contrapose! h
  exact Finset.prod_eq_one h

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem mem_sum {a : M} {s : Finset ι} {m : ι → Multiset M} :
    a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  induction s using Finset.cons_induction with grind

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i := (@isCompl_compl _ s _).symm.prod_mul_prod f

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· ∈ s)] (f : ι → M) (g : s → M)
    (w : ∀ x (hx : x ∈ s), f x = g ⟨x, hx⟩) (w' : ∀ x ∉ s, f x = 1) : ∏ i, f i = ∏ i, g i := by
  rw [← Finset.prod_subset s.toFinset.subset_univ (by simpa), Finset.prod_subtype (p := (· ∈ s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_dvd_prod_of_dvd (f g : ι → M) (h : ∀ i ∈ s, f i ∣ g i) :
    ∏ i ∈ s, f i ∣ ∏ i ∈ s, g i := Multiset.prod_dvd_prod_of_dvd _ _ h

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) :
    ∏ x ∈ s, f x = if a ∈ s then f a else 1 := by
  by_cases h : a ∈ s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : ∀ b ∈ s, f b = 1 := by grind
    simp +contextual [h₀]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_mul_of_mem {s : Finset ι} {f : ι → M} (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' ⊆ s := by grind
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_one_iff [Subsingleton Mˣ] : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction s using Finset.cons_induction <;> simp [*]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_erase_eq_div {a : ι} (h : a ∈ s) : ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  rw [eq_div_iff_mul_eq', Finset.prod_erase_mul _ _ h]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
    [MulLeftStrictMono κ] {s : Finset ι} {d : ι} (hd : d ∈ s) {f : ι → κ}
    (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by
  conv in ∏ m ∈ s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by rw [mul_comm, Finset.mul_prod_erase s f h]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_extend_by_one [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := (Finset.prod_congr rfl) fun _i hi => if_pos hi

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter_ne_one (s : Finset ι) [∀ x, Decidable (f x ≠ 1)] :
    ∏ x ∈ s with f x ≠ 1, f x = ∏ x ∈ s, f x := Finset.prod_filter_of_ne fun _ _ => id

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter_not_mul_prod_filter (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    [∀ x, Decidable (¬p x)] (f : ι → M) :
    (∏ x ∈ s with ¬p x, f x) * ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x := by
  rw [mul_comm, Finset.prod_filter_mul_prod_filter_not]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ → ι} {g : ι → M}
    (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  refine Finset.prod_image_of_pairwise_eq_one <| hf_disj.imp fun i j hdisj hfij ↦ ?_
  rw [Function.onFun, ← hfij, disjoint_self] at hdisj
  rw [hdisj, hg_bot]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {I : Finset κ}
    (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  rw [Finset.prod_image']
  exact fun n hnI => (Finset.prod_filter_of_pairwise_eq_one hnI hf).symm

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_insert' [DecidableEq ι] (h : a ∉ s) :
    Finset.prod (insert a s) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_insert h]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : ι → M) [DecidablePred (· ∈ s)] :
    (∏ i, if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  rw [← Finset.prod_filter]; congr; grind

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_list_count [DecidableEq M] (s : List M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by simpa using Finset.prod_list_map_count s id

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_mul_prod_comm (f g h i : ι → M) :
    (∏ a ∈ s, f a * g a) * ∏ a ∈ s, h a * i a = (∏ a ∈ s, f a * h a) * ∏ a ∈ s, g a * i a := by
  simp_rw [Finset.prod_mul_distrib, mul_mul_mul_comm]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i := IsCompl.prod_mul_prod isCompl_compl f

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_count [DecidableEq M] (s : Multiset M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  convert Finset.prod_multiset_map_count s id
  rw [Multiset.map_id]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
    (f : ι → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [Finset.prod_list_map_count l f]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_ninvolution (g : ι → ι) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 := Finset.prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_of_injective (e : ι → κ) (he : Function.Injective e) (f : ι → M) (g : κ → M)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j := Finset.prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ ↦ h i)

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_partition (R : Setoid ι) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_induction (f s : ℕ → M) (base : s 0 = 1)
    (n : ℕ) (step : ∀ k < n, s (k + 1) = s k * f k) :
    ∏ k ∈ Finset.range n, f k = s n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ, step _ (Nat.lt_succ_self _), hk]
    exact fun _ hl ↦ step _ (Nat.lt_succ_of_lt hl)

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) : ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [eq_div_iff_mul_eq', Finset.prod_sdiff h]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι → M}

theorem prod_sdiff_ne_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i ≠ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≠ ∏ i ∈ t, f i := Finset.prod_sdiff_eq_prod_sdiff_iff.not

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i := (Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x := haveI := Classical.decEq ι
  Finset.prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subset_one_on_sdiff [DecidableEq ι] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i ∈ s₁, f i = ∏ i ∈ s₂, g i := by
  rw [← Finset.prod_sdiff h, Finset.prod_eq_one hg, one_mul]
  exact Finset.prod_congr rfl hfg

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_subsingleton [Subsingleton ι] (f : ι → M) (a : ι) : ∏ x : ι, f x = f a := by
  have : Unique ι := uniqueOfSubsingleton a
  rw [Fintype.prod_unique f, Subsingleton.elim default a]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : ∀ x, x ∈ s ↔ p x)
    (f : ι → M) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  obtain rfl : p = (· ∈ s) := by simp [h]
  rw [← Finset.prod_coe_sort]
  congr!

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subtype_map_embedding {p : ι → Prop} {s : Finset { x // p x }} {f : { x // p x } → M}
    {g : ι → M} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x ∈ s.map (Function.Embedding.subtype _), g x) = ∏ x ∈ s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_subtype_mul_prod_subtype (p : ι → Prop) (f : ι → M) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem prod_sum {ι : Type*} [CommMonoid M] (f : ι → Multiset M) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by
  induction s using Finset.cons_induction with grind

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι ⊕ κ)) (f : ι ⊕ κ → M) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by
  rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum, Finset.toLeft_disjSum,
    Finset.toRight_disjSum]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι → M) :
    ∀ {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨notMem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp notMem), prod_toFinset _ hl]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι → M) (h : s.Nonempty) :
    ∏ x ∈ s, f x = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : ℕ)).symm

end

section

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem toFinset_sum_count_nsmul_eq (s : Multiset ι) :
    ∑ a ∈ s.toFinset, s.count a • {a} = s := by
  rw [← Finset.sum_multiset_map_count, Multiset.sum_map_singleton]

end
