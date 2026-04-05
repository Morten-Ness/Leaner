import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem _root_.SubmonoidClass.finsuppProd_mem {S : Type*} [SetLike S N] [SubmonoidClass S N]
    (s : S) (f : α →₀ M) (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s := prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)

-- Note: Using `gcongr` since `congr` doesn't accept this lemma.

