import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem smul_set_prod {M α : Type*} [SMul M α] [SMul M β] (c : M) (s : Set α) (t : Set β) :
    c • (s ×ˢ t) = (c • s) ×ˢ (c • t) := prodMap_image_prod (c • ·) (c • ·) s t

