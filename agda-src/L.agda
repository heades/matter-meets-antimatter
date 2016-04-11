module L where

open import empty
open import snoc renaming ([_] to [_]L ; _++_ to _++L_; _::_ to _::L_)
open import list renaming ([_] to [_]R ; _++_ to _++R_; _::_ to _::R_)

open import graphs

data L-Form : Set where
  One : L-Form
  Zero : L-Form
  _×_ : L-Form → L-Form → L-Form
  _+_ : L-Form → L-Form → L-Form  
  _⇒_ : L-Form → L-Form → L-Form
  _-_ : L-Form → L-Form → L-Form  
  
-- Bi-intuitionistic left and right contexts:
L-LCtx : Set
L-LCtx = Snoc (Σ World (λ _ → L-Form))

L-RCtx : Set
L-RCtx = 𝕃 (Σ World (λ _ → L-Form))

worldInLLCtx : World → L-LCtx → Set
worldInLLCtx = inPairSnocFst _=ℕ_

worldInLRCtx : World → L-RCtx → Set
worldInLRCtx w c = inPairListFst _=ℕ_ w c

data ⟨_⟩_⊢L_ : Graph → L-LCtx → L-RCtx → Set where
    L-RL : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}
      → ⟨ Gr ::L (w , w) ⟩ Γ ⊢L Δ
      → ⟨ Gr ⟩ Γ ⊢L Δ

    L-TS : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w₁ w₂ w₃ : World}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr ::L (w₁ , w₃) ⟩ Γ ⊢L Δ
      → ⟨ Gr ⟩ Γ ⊢L Δ

    L-ML : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w₁ w₂ : World}{A : L-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (Γ ::L (w₁ , A) ::L (w₂ , A)) ⊢L Δ
      → ⟨ Gr ⟩ (Γ ::L (w₁ , A)) ⊢L Δ

    L-MR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w₁ w₂ : World}{A : L-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Γ ⊢L ((w₂ , A) ::R (w₁ , A) ::R Δ)
      → ⟨ Gr ⟩ Γ ⊢L ((w₁ , A) ::R Δ)

  -- Structural Rules:
    L-WKL : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}{A : L-Form}
      → ⟨ Gr ⟩ Γ ⊢L Δ
      → ⟨ Gr ⟩ (Γ ::L (w , A)) ⊢L Δ

    L-WKR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}{A : L-Form}
      → ⟨ Gr ⟩ Γ ⊢L Δ
      → ⟨ Gr ⟩ Γ ⊢L ((w , A) ::R Δ)

    L-CTRL : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}{A : L-Form}
      → ⟨ Gr ⟩ (Γ ::L (w , A) ::L (w , A)) ⊢L Δ
      → ⟨ Gr ⟩ (Γ ::L (w , A)) ⊢L Δ

    L-CTRR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}{A : L-Form}
      → ⟨ Gr ⟩ Γ ⊢L ((w , A) ::R (w , A) ::R Δ)
      → ⟨ Gr ⟩ Γ ⊢L ((w , A) ::R Δ)

    L-EXL : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ : L-RCtx}{w₁ w₂ : World}{A B : L-Form}
      → ⟨ Gr ⟩ ((Γ₁ ::L (w₁ , A) ::L (w₂ , B)) ++L Γ₂) ⊢L Δ 
      → ⟨ Gr ⟩ ((Γ₁ ::L (w₂ , B) ::L (w₁ , A)) ++L Γ₂) ⊢L Δ 

    L-EXR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w₁ w₂ : World}{A B : L-Form}
      → ⟨ Gr ⟩ Γ ⊢L (Δ₁ ++R ((w₁ , A) ::R (w₂ , B) ::R Δ₂))
      → ⟨ Gr ⟩ Γ ⊢L (Δ₁ ++R ((w₂ , B) ::R (w₁ , A) ::R Δ₂))
      
  -- Identity and Cut Rules:
    L-ID : ∀{Gr : Graph}{w : World}{A : L-Form}
      → ⟨ Gr ⟩ [ (w , A) ]L ⊢L [ (w , A) ]R

    L-Cut : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w : World}{A : L-Form}
      → ⟨ Gr ⟩ Γ₂ ⊢L ((w , A) ::R Δ₂)
      → ⟨ Gr ⟩ (Γ₁ ::L (w , A)) ⊢L Δ₁
      → ⟨ Gr ⟩ (Γ₁ ++L Γ₂) ⊢L (Δ₁ ++R Δ₂)

  -- Conjunction Rules:
    L-IL : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}
      → ⟨ Gr ⟩ Γ ⊢L Δ 
      → ⟨ Gr ⟩ (Γ ::L (w , One)) ⊢L Δ

    L-IR : ∀{Gr : Graph}{w : World}
      → ⟨ Gr ⟩ [] ⊢L [ (w , One) ]R 

    L-TL : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ : L-RCtx}{w : World}{A B : L-Form}
      → ⟨ Gr ⟩ ((Γ₁ ::L (w , A) ::L (w , B)) ++L Γ₂) ⊢L Δ
      → ⟨ Gr ⟩ ((Γ₁ ::L (w , A × B)) ++L Γ₂) ⊢L Δ

    L-TR : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w : World}{A B : L-Form}
      → ⟨ Gr ⟩ Γ₁ ⊢L ((w , A) ::R Δ₁)
      → ⟨ Gr ⟩ Γ₂ ⊢L ((w , B) ::R Δ₂)
      → ⟨ Gr ⟩ (Γ₁ ++L Γ₂) ⊢L ((w , A × B) ::R (Δ₁ ++R Δ₂))

  -- Disjunction and Par Rules
    L-FL : ∀{Gr : Graph}{w : World}
      → ⟨ Gr ⟩ [ (w , Zero) ]L ⊢L []

    L-FLR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w : World}
      → ⟨ Gr ⟩ Γ ⊢L Δ
      → ⟨ Gr ⟩ Γ ⊢L ((w , Zero) ::R Δ)

    L-PL : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w : World}{A B : L-Form}
      → ⟨ Gr ⟩ (Γ₁ ::L (w , A)) ⊢L Δ₁
      → ⟨ Gr ⟩ (Γ₂ ::L (w , B)) ⊢L Δ₂
      → ⟨ Gr ⟩ ((Γ₁ ++L Γ₂) ::L (w , A + B)) ⊢L (Δ₁ ++R Δ₂)

    L-PR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w : World}{A B : L-Form}
      → ⟨ Gr ⟩ Γ ⊢L (Δ₁ ++R ((w , A) ::R (w , B) ::R Δ₂))
      → ⟨ Gr ⟩ Γ ⊢L (Δ₁ ++R ((w , A + B) ::R Δ₂))

  -- Implication Rules:
    L-ImpL : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w₁ w₂ : World}{A B : L-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Γ₁ ⊢L ((w₂ , A) ::R Δ₁)
      → ⟨ Gr ⟩ (Γ₂ ::L (w₂ , B)) ⊢L Δ₂
      → ⟨ Gr ⟩ ((Γ₁ ++L Γ₂) ::L (w₁ , A ⇒ B)) ⊢L (Δ₁ ++R Δ₂)

    L-ImpR : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w₁ w₂ : World}{A B : L-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInLLCtx w₂ Γ) → ⊥)
      → ((worldInLRCtx w₂ Δ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::L (w₁ , w₂) ⟩ (Γ ::L (w₂ , A)) ⊢L ((w₂ , B) ::R Δ) 
      → ⟨ Gr ⟩ Γ ⊢L ((w₁ , A ⇒ B) ::R Δ)

  -- Co-implication Rules:
    L-SL : ∀{Gr : Graph}{Γ : L-LCtx}{Δ : L-RCtx}{w₁ w₂ : World}{A B : L-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInLLCtx w₂ Γ) → ⊥)
      → ((worldInLRCtx w₂ Δ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::L (w₂ , w₁) ⟩ (Γ ::L (w₂ , A)) ⊢L ((w₂ , B) ::R Δ)
      → ⟨ Gr ⟩ (Γ ::L (w₁ , A - B)) ⊢L Δ

    L-SR : ∀{Gr : Graph}{Γ₁ Γ₂ : L-LCtx}{Δ₁ Δ₂ : L-RCtx}{w₁ w₂ : World}{A B : L-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Γ₁ ⊢L ((w₂ , A) ::R Δ₁)
      → ⟨ Gr ⟩ (Γ₂ ::L (w₂ , B)) ⊢L Δ₂
      → ⟨ Gr ⟩ (Γ₁ ++L Γ₂) ⊢L ((w₁ , A - B) ::R (Δ₁ ++R Δ₂))      
