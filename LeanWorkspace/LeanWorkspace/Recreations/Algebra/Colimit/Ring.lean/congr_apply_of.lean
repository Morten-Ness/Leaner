import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

variable {f : ∀ i j, i ≤ j → G i →+* G j}

variable {G' : ι → Type*} [∀ i, CommRing (G' i)]

variable {f' : ∀ i j, i ≤ j → G' i →+* G' j}

variable {G'' : ι → Type*} [∀ i, CommRing (G'' i)]

variable {f'' : ∀ i j, i ≤ j → G'' i →+* G'' j}

theorem congr_apply_of (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    Ring.DirectLimit.congr e he (of G _ i g) = of G' (fun _ _ h ↦ f' _ _ h) i (e i g) := map_apply_of _ he _

