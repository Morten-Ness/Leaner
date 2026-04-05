import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_apply_dite {p : ι → Prop} [DecidablePred p]
    [DecidablePred fun x => ¬p x] (f : ∀ x : ι, p x → γ) (g : ∀ x : ι, ¬p x → γ) (h : γ → M) :
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) := calc
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x ∈ s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x ∈ s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x ∈ s | p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x : {x ∈ s | ¬p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ (prod_attach _ _).symm (prod_attach _ _).symm
    _ = (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
          ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x _hx ↦
        congr_arg h (dif_pos <| by simpa using (mem_filter.mp x.2).2))
        (prod_congr rfl fun x _hx => congr_arg h (dif_neg <| by simpa using (mem_filter.mp x.2).2))

