import Mathlib

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem comp_liftAddHom [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : N →+ P)
    (f : α → M →+ N) :
    g.comp ((Finsupp.liftAddHom (α := α) (M := M) (N := N)) f) =
      (Finsupp.liftAddHom (α := α) (M := M) (N := P)) fun a => g.comp (f a) :=
  Finsupp.liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [Finsupp.liftAddHom_symm_apply, AddMonoidHom.comp_assoc, Finsupp.liftAddHom_comp_single]

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem liftAddHom_apply [AddZeroClass M] [AddCommMonoid N] (F : α → M →+ N) (f : α →₀ M) :
    (Finsupp.liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x :=
  rfl

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m := map_sum (Multiset.mapAddMonoidHom m) _ f.support

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) := map_sum Multiset.sumAddMonoidHom _ f.support

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  classical exact Finsupp.prod_add_index (fun a _ => h_zero a) fun a _ => h_add a

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    (h : α → Multiplicative M →* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) := Finsupp.prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_inv [Zero M] [CommGroup G] {f : α →₀ M} {h : α → M → G} :
    (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹ := (map_prod (MonoidHom.id G)⁻¹ _ _).symm

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N]
    {f : α →₀ M} {g : α → M → N} {n₁ n₂ : N}
    (a : α) (ha : a ∈ f.support)
    (h : g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ := by
  classical
  exact Finset.prod_mul_eq_prod_mul_of_exists a ha h

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a := Finsupp.prod_fintype f _ fun _ ↦ pow_zero _

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_pow_pos_of_zero_notMem_support {f : ℕ →₀ ℕ} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) := Nat.pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_sum_index [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α →₀ M}
    {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h := (Finsupp.prod_finset_sum_index h_zero h_add).symm

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_unique [Unique α] {f : α →₀ M} {g : α → M → N} (h₁ : f default = 0 → g default 0 = 1) :
    f.prod g = g default (f default) := Finsupp.prod_eq_single _ (fun a ↦ by simp [Subsingleton.elim a default]) h₁

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α →₀ ℤ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a := Finsupp.prod_fintype f _ fun _ ↦ zpow_zero _

end

section

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem sum_sub_index [AddGroup β] [AddCommGroup γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h := ((Finsupp.liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

end
