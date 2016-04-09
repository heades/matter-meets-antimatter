module BiLNL where

open import nat renaming (_+_ to _+ℕ_)
open import list
open import product hiding (_×_)
open import empty
open import unit
open import bool

World : Set
World = ℕ
  
Graph : Set
Graph = 𝕃 (World ∧ World)

_[_]_ : World → Graph → World → Set
w₁ [ [] ] w₂ = ⊥
w₁ [ (a , b) :: G ] w₂ with a =ℕ w₁ | b =ℕ w₂
w₁ [ (a , b) :: G ] w₂ | tt | tt = ⊤
w₁ [ (a , b) :: G ] w₂ | _ | _ = ⊥

data I-Form : Set where
  True : I-Form
  _×_ : I-Form → I-Form → I-Form
  _⇒_ : I-Form → I-Form → I-Form

data C-Form : Set where
  False : C-Form
  _+_ : C-Form → C-Form → C-Form
  _-_ : C-Form → C-Form → C-Form
  
data BiLNL-Form : Set where

data L-Form : Set where

