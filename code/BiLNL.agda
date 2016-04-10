module BiLNL where

open import nat renaming (_+_ to _+ℕ_)
open import snoc renaming ([_] to [_]I ; _++_ to _++I_; _::_ to _::I_)
open import list renaming ([_] to [_]C ; _++_ to _++C_; _::_ to _::C_)
open import product hiding (_×_)
open import empty
open import unit
open import bool

World : Set
World = ℕ
  
Graph : Set
Graph = Snoc (World ∧ World)

_⟨_⟩_ : World → Graph → World → Set
w₁ ⟨ [] ⟩ w₂ = ⊥
w₁ ⟨ G ::I (a , b) ⟩ w₂ with a =ℕ w₁ | b =ℕ w₂
w₁ ⟨ G ::I (a , b) ⟩ w₂ | tt | tt = ⊤
w₁ ⟨ G ::I (a , b) ⟩ w₂ | _ | _ = ⊥

worldInGr : World → Graph → Set
worldInGr w [] = ⊥
worldInGr w (G ::I (w₁ , w₂)) with w =ℕ w₁ | w =ℕ w₂
... | tt | _ = ⊤
... | _ | tt = ⊤
... | _ | _ = worldInGr w G

_=W_ : World → World → Set
w₁ =W w₂ with w₁ =ℕ w₂
... | tt = ⊤
... | ff = ⊥

mutual
  -- Intuitionistic formulas:
  data I-Form : Set where
    True : I-Form
    _×_ : I-Form → I-Form → I-Form
    _⇒_ : I-Form → I-Form → I-Form
    G   : BiL-Form → I-Form

  -- Co-intuitionistic formulas:
  data C-Form : Set where
    False : C-Form
    _+_ : C-Form → C-Form → C-Form
    _≺_ : C-Form → C-Form → C-Form
    H   : BiL-Form → C-Form

  -- Bi-intuitionistic Linear Formulas:
  data BiL-Form : Set where
    I : BiL-Form
    J : BiL-Form
    _⊗_ : BiL-Form → BiL-Form → BiL-Form
    _⊕_ : BiL-Form → BiL-Form → BiL-Form
    _⊸_ : BiL-Form → BiL-Form → BiL-Form
    _≺L_ : BiL-Form → BiL-Form → BiL-Form
    
I-Ctx : Set
I-Ctx = Snoc (World ∧ I-Form)

worldInICtx : World → I-Ctx → Set
worldInICtx = inPairSnocFst _=ℕ_

C-Ctx : Set
C-Ctx = 𝕃 (World ∧ C-Form)

worldInCCtx : World → C-Ctx → Set
worldInCCtx w [] = ⊥
worldInCCtx w ((a , b) ::C c) with w =ℕ a
... | tt = ⊤
... | ff = ⊥

BiL-Ctx : Set
BiL-Ctx = Snoc (World ∧ BiL-Form)

worldInBiLCtx : World → BiL-Ctx → Set
worldInBiLCtx = inPairSnocFst _=ℕ_

mutual
  -- Intuitionistic fragment of BiLNL logic:
  data ⟨_⟩_⊢I_ : Graph → I-Ctx → (World ∧ I-Form) → Set where
    I-RL : ∀{Gr : Graph}{Θ : I-Ctx}{w1 w2 : World}{Y : I-Form}
      → ⟨ Gr ::I (w1 , w1) ⟩ Θ ⊢I (w2 , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w2 , Y)

    I-TS : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ w₃ w : World}{Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr ::I (w₁ , w₃) ⟩ Θ ⊢I (w , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w , Y)

    I-ID : ∀{Gr : Graph}{w : World}{Y : I-Form}
      → ⟨ Gr ⟩ [ (w , Y) ]I ⊢I (w , Y)

    I-Cut : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₂ w₁ : World}{X Z : I-Form}
      → ⟨ Gr ⟩ Θ₂ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₁ ::I (w₂ , X)) ⊢I (w₁ , Z)
      → ⟨ Gr ⟩ (Θ₁ ++I Θ₂) ⊢I (w₁ , Z)

    I-WK : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ ::I (w₂ , X)) ⊢I (w₁ , Y)

    I-CR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ (Θ ::I (w₂ , X) ::I (w₂ , X)) ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ ::I (w₂ , X)) ⊢I (w₁ , Y)

    I-EX : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₁ w₂ w : World}{X Y Z : I-Form}
      → ⟨ Gr ⟩ ((Θ₁ ::I (w₂ , Y) ::I (w₁ , X)) ++I Θ₂) ⊢I (w , Z)
      → ⟨ Gr ⟩ ((Θ₁ ::I (w₁ , X) ::I (w₂ , Y)) ++I Θ₂) ⊢I (w , Z)

    I-ML : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ w : World}{X Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (Θ ::I (w₁ , X) ::I (w₂ , X)) ⊢I (w , Y)
      → ⟨ Gr ⟩ ((Θ ::I (w₁ , X))) ⊢I (w , Y)

    I-MR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{Y : I-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ ⊢I (w₂ , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)

    I-TL : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ ::I (w₂ , True)) ⊢I (w₁ , Y)

    I-TR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w , True)

    I-PL : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y Z : I-Form}
      → ⟨ Gr ⟩ (Θ ::I (w₁ , X) ::I (w₁ , Y)) ⊢I (w₂ , Z)
      → ⟨ Gr ⟩ (Θ ::I (w₁ , X × Y)) ⊢I (w₂ , Z)

    I-PR : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w : World}{X Y : I-Form}
      → ⟨ Gr ⟩ Θ₁ ⊢I (w , X)
      → ⟨ Gr ⟩ Θ₂ ⊢I (w , Y)
      → ⟨ Gr ⟩ (Θ₁ ++I Θ₂) ⊢I (w , X × Y)

    I-IL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₁ w₂ w : World}{X Y Z : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Θ₂ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₁ ::I (w₂ , Y)) ⊢I (w , Z)
      → ⟨ Gr ⟩ (Θ₁ ++I Θ₂ ::I (w₁ , X ⇒ Y)) ⊢I (w , Z)

    I-IR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInICtx w₂ Θ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::I (w₁ , w₂) ⟩ (Θ ::I (w₂ , X)) ⊢I (w₂ , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , X ⇒ Y)

    I-GR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ [] ⊢LL [ (w , A) ]I ∣ []
      → ⟨ Gr ⟩ Θ ⊢I (w , (G A)) 

  -- Co-intuitionistic fragment of BiLNL logic:
  data ⟨_⟩_⊢C_ : Graph → (World ∧ C-Form) → C-Ctx → Set where
    C-RL : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → ⟨ Gr ::I (w₁ , w₁) ⟩ (w₂ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₂ , S) ⊢C Ψ

    C-TS : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ w₃ w : World}{S : C-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr ::I (w₁ , w₃) ⟩ (w , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w , S) ⊢C Ψ

    C-ID : ∀{Gr : Graph}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ (w , S) ⊢C [ (w , S) ]C

    C-Cut : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::C Ψ₂)
      → ⟨ Gr ⟩ (w₂ , T) ⊢C Ψ₁      
      → ⟨ Gr ⟩ (w₁ , S) ⊢C (Ψ₁ ++C Ψ₂)

    C-WK : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::C Ψ)

    C-CR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::C (w₂ , T) ::C Ψ)
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::C Ψ)

    C-EX : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ w : World}{R S T : C-Form}
      → ⟨ Gr ⟩ (w , R) ⊢C (Ψ₁ ++C (w₁ , S) ::C (w₂ , T) ::C Ψ₂)
      → ⟨ Gr ⟩ (w , R) ⊢C (Ψ₁ ++C (w₂ , T) ::C (w₁ , S) ::C Ψ₂)

    C-ML : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (w₂ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₁ , S) ⊢C Ψ

    C-MR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ w : World}{S T : C-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ (w , S) ⊢C ((w₂ , T) ::C (w₁ , T) ::C Ψ)
      → ⟨ Gr ⟩ (w , S) ⊢C ((w₁ , T) ::C Ψ)

    C-FL : ∀{Gr : Graph}{Ψ : C-Ctx}{w : World}
      → ⟨ Gr ⟩ (w , False) ⊢C Ψ

    C-FR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , False) ::C Ψ)

    C-DL : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w , S) ⊢C Ψ₁
      → ⟨ Gr ⟩ (w , T) ⊢C Ψ₂
      → ⟨ Gr ⟩ (w , S + T) ⊢C (Ψ₁ ++C Ψ₂)

    C-DR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{R S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , R) ⊢C ((w₂ , S) ::C (w₂ , T) ::C Ψ)
      → ⟨ Gr ⟩ (w₁ , R) ⊢C ((w₂ , S + T) ::C Ψ)

    C-SL : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInCCtx w₂ Ψ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::I (w₂ , w₁) ⟩ (w₂ , S) ⊢C ((w₂ , T) ::C Ψ)
      → ⟨ Gr ⟩ (w₁ , S ≺ T) ⊢C Ψ

    C-SR : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ w : World}{R S T : C-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ (w , R) ⊢C ((w₂ , S) ::C Ψ₂)
      → ⟨ Gr ⟩ (w₂ , T) ⊢C Ψ₁
      → ⟨ Gr ⟩ (w , R) ⊢C ((w₁ , S ≺ T) ::C Ψ₁ ++C Ψ₂)

    C-HL : ∀{Gr : Graph}{Ψ : C-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ [] ∣ [ (w , A) ]I ⊢LL [] ∣ Ψ
      → ⟨ Gr ⟩ (w , H A) ⊢C Ψ

  -- Linear Core of BiLNL logic:
  data ⟨_⟩_∣_⊢LL_∣_ : Graph → I-Ctx → BiL-Ctx → BiL-Ctx → C-Ctx → Set where
