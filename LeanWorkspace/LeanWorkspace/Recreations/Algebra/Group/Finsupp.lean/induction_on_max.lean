import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

variable [LinearOrder ι] {motive : (ι →₀ M) → Prop}

theorem induction_on_max (f : ι →₀ M) (zero : motive 0)
    (Finsupp.single_add : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 →
      motive f → motive (single a b + f)) : motive f := by
  suffices ∀ (s) (f : ι →₀ M), f.support = s → motive f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase, hs, erase_insert (fun ha => (hm a ha).false)]
    rw [← Finsupp.single_add_erase a f]
    refine Finsupp.single_add _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff, hs]
    exact mem_insert_self a s

