import Mathlib

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (FreeMonoid.of x) = g (FreeMonoid.of x)) : f = g := MonoidHom.ext fun l ↦ FreeMonoid.recOn l (f.map_one.trans g.map_one.symm)
    (fun x xs hxs ↦ by simp only [h, hxs, map_mul])

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (FreeMonoid.lift f x) = FreeMonoid.lift (g ∘ f) x := DFunLike.ext_iff.1 (FreeMonoid.comp_lift g f) x

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem inductionOn' {p : FreeMonoid α → Prop} (a : FreeMonoid α)
    (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (FreeMonoid.of b * a)) : p a := List.rec one (fun _ _ tail_ih => mul_of _ _ tail_ih) a

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_map {α₁ : Type*} {g : α₁ → α} {x : FreeMonoid α₁} :
    FreeMonoid.map f (FreeMonoid.map g x) = FreeMonoid.map (f ∘ g) x := by
  unfold FreeMonoid.map
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, FreeMonoid.toList_ofList, List.map_map]

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_surjective {f : α → β} : Function.Surjective (FreeMonoid.map f) ↔ Function.Surjective f := by
  constructor
  · intro fs d
    rcases fs (FreeMonoid.of d) with ⟨b, hb⟩
    induction b using FreeMonoid.inductionOn' with
    | one =>
      have H := congr_arg FreeMonoid.length hb
      simp only [FreeMonoid.length_one, FreeMonoid.length_of, Nat.zero_ne_one, map_one] at H
    | mul_of head _ _ =>
      simp only [map_mul, FreeMonoid.map_of] at hb
      use head
      have H := congr_arg FreeMonoid.length hb
      simp only [FreeMonoid.length_mul, FreeMonoid.length_of, add_eq_left, FreeMonoid.length_eq_zero] at H
      rw [H, mul_one] at hb
      exact FreeMonoid.of_injective hb
  intro fs d
  induction d using FreeMonoid.inductionOn' with
  | one => use 1; rfl
  | mul_of head tail ih =>
    specialize fs head
    rcases fs with ⟨a, rfl⟩
    rcases ih with ⟨b, rfl⟩
    use FreeMonoid.of a * b
    rfl

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_flatten (xs : List (List α)) : FreeMonoid.ofList xs.flatten = (xs.map FreeMonoid.ofList).prod := FreeMonoid.toList.injective <| by simp

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_smul (f : α → β → β) (l : List α) (b : β) :
    haveI := FreeMonoid.mkMulAction f
    FreeMonoid.ofList l • b = l.foldr f b := rfl

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem of_ne_one (a : α) : FreeMonoid.of a ≠ 1 := by
  intro h
  have := congrArg FreeMonoid.length h
  simp only [FreeMonoid.length_of, FreeMonoid.length_one, Nat.succ_ne_self] at this

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem of_smul (f : α → β → β) (x : α) (y : β) :
    (haveI := FreeMonoid.mkMulAction f
    FreeMonoid.of x • y) = f x y := rfl

end

section

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := FreeMonoid.mkMulAction f
    l • b = l.toList.foldr f b := rfl

end
