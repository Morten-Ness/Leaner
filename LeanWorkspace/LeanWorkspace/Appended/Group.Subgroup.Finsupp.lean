import Mathlib

section

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem exists_finsupp_of_mem_closure_range (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · simp [zpow_add]
  | inv x hx hx' =>
    obtain ⟨a, rfl⟩ := hx'
    use -a
    rw [Finsupp.prod_neg_index]
    · simp
    · simp

end

section

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem exists_of_mem_closure_range [Fintype ι] (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := Subgroup.exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

end

section

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_iff_of_fintype {s : Set M} [Fintype s] :
    x ∈ closure s ↔ ∃ a : s → ℤ, x = ∏ i : s, i.1 ^ a i := by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact Subgroup.mem_closure_range_iff_of_fintype

end

section

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_range_iff :
    x ∈ closure (Set.range f) ↔ ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  refine ⟨Subgroup.exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi ↦ zpow_mem (subset_closure (Set.mem_range_self i)) _

end

section

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_range_iff_of_fintype [Fintype ι] :
    x ∈ closure (Set.range f) ↔ ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left, Subgroup.mem_closure_range_iff]
  simp

end
