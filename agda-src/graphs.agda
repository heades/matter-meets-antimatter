module graphs where

open import nat renaming (_+_ to _+ℕ_) public
open import snoc public
open import product public hiding (_×_ ; _∧_)
open import unit 
open import empty
open import bool

World : Set
World = ℕ
  
Graph : Set
Graph = Snoc (Σ World (λ _ → World))

_⟨_⟩_ : World → Graph → World → Set
w₁ ⟨ [] ⟩ w₂ = ⊥
w₁ ⟨ G :: (a , b) ⟩ w₂ with a =ℕ w₁ | b =ℕ w₂
w₁ ⟨ G :: (a , b) ⟩ w₂ | tt | tt = ⊤
w₁ ⟨ G :: (a , b) ⟩ w₂ | _ | _ = ⊥

worldInGr : World → Graph → Set
worldInGr w [] = ⊥
worldInGr w (G :: (w₁ , w₂)) with w =ℕ w₁ | w =ℕ w₂
... | tt | _ = ⊤
... | _ | tt = ⊤
... | _ | _ = worldInGr w G

_=W_ : World → World → Set
w₁ =W w₂ with w₁ =ℕ w₂
... | tt = ⊤
... | ff = ⊥
