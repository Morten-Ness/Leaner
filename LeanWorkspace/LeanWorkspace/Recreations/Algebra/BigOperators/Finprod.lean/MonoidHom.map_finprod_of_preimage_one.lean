import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem MonoidHom.map_finprod_of_preimage_one (f : M →* N) (hf : ∀ x, f x = 1 → x = 1) (g : α → M) :
    f (∏ᶠ i, g i) = ∏ᶠ i, f (g i) := by
  by_cases hg : HasFiniteMulSupport <| g ∘ PLift.down; · exact f.map_finprod_plift g hg
  rw [finprod, dif_neg, f.map_one, finprod, dif_neg]
  exacts [Infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

