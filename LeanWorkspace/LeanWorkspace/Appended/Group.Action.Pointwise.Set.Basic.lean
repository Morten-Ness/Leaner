import Mathlib

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  simpa using Set.disjoint_smul_set (a := a) (t := a⁻¹ • t)

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  simpa using Set.disjoint_smul_set (a := a) (s := a⁻¹ • s)

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s := (Function.Surjective.iSup_congr _ inv_surjective) fun _ ↦ rfl

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem mem_smul_set_inv {s : Set α} : a ∈ b • s⁻¹ ↔ b ∈ a • s := by
  simp [Set.mem_smul_set_iff_inv_smul_mem]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t := ((MulAction.toPerm a).image_symm_eq_preimage _).symm

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

theorem smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [Set.mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_inter_nonempty_iff' {s t : Set α} {x : α} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [Set.smul_inter_nonempty_iff, div_eq_mul_inv]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s := (MulAction.injective _).mem_set_image

end

section

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  simp_rw [Set.compl_eq_univ_diff, Set.smul_set_sdiff, Set.smul_set_univ]

end

section

open scoped Pointwise

variable {F α β γ : Type*}

theorem smul_set_pi_of_isUnit {M ι : Type*} {α : ι → Type*} [Monoid M] [∀ i, MulAction M (α i)]
    {c : M} (hc : IsUnit c) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := by
  lift c to Mˣ using hc
  exact Set.smul_set_pi c I s

end
