module BiLNL where

open import nat renaming (_+_ to _+ℕ_)
open import snoc renaming ([_] to [_]L ; _++_ to _++L_; _::_ to _::L_)
open import list renaming ([_] to [_]R ; _++_ to _++R_; _::_ to _::R_)
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
w₁ ⟨ G ::L (a , b) ⟩ w₂ with a =ℕ w₁ | b =ℕ w₂
w₁ ⟨ G ::L (a , b) ⟩ w₂ | tt | tt = ⊤
w₁ ⟨ G ::L (a , b) ⟩ w₂ | _ | _ = ⊥

worldInGr : World → Graph → Set
worldInGr w [] = ⊥
worldInGr w (G ::L (w₁ , w₂)) with w =ℕ w₁ | w =ℕ w₂
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
    One : I-Form
    _×_ : I-Form → I-Form → I-Form
    _⇒_ : I-Form → I-Form → I-Form
    G   : BiL-Form → I-Form

  -- Co-intuitionistic formulas:
  data C-Form : Set where
    Zero : C-Form
    _+_ : C-Form → C-Form → C-Form
    _≺_ : C-Form → C-Form → C-Form
    H   : BiL-Form → C-Form

  -- Bi-intuitionistic Linear Formulas:
  data BiL-Form : Set where
    True : BiL-Form
    False : BiL-Form
    F : I-Form → BiL-Form
    J : C-Form → BiL-Form    
    _⊗_ : BiL-Form → BiL-Form → BiL-Form
    _⊕_ : BiL-Form → BiL-Form → BiL-Form
    _⊸_ : BiL-Form → BiL-Form → BiL-Form
    _≺L_ : BiL-Form → BiL-Form → BiL-Form

-- Intuitionistic contexts:
I-Ctx : Set
I-Ctx = Snoc (World ∧ I-Form)

worldInICtx : World → I-Ctx → Set
worldInICtx = inPairSnocFst _=ℕ_

-- Co-intuitionistic contexts:
C-Ctx : Set
C-Ctx = 𝕃 (World ∧ C-Form)

worldInCCtx : World → C-Ctx → Set
worldInCCtx w c = inPairListFst _=ℕ_ w c

-- Bi-intuitionistic left and right contexts:
BiL-LCtx : Set
BiL-LCtx = Snoc (World ∧ BiL-Form)

BiL-RCtx : Set
BiL-RCtx = 𝕃 (World ∧ BiL-Form)

worldInBiLLCtx : World → BiL-LCtx → Set
worldInBiLLCtx = inPairSnocFst _=ℕ_

worldInBiLRCtx : World → BiL-RCtx → Set
worldInBiLRCtx w c = inPairListFst _=ℕ_ w c

-- The inference rules for BiLNL Logic:

mutual
  -- Intuitionistic fragment of BiLNL logic:
  data ⟨_⟩_⊢I_ : Graph → I-Ctx → (World ∧ I-Form) → Set where
    I-RL : ∀{Gr : Graph}{Θ : I-Ctx}{w1 w2 : World}{Y : I-Form}
      → ⟨ Gr ::L (w1 , w1) ⟩ Θ ⊢I (w2 , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w2 , Y)

    I-TS : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ w₃ w : World}{Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr ::L (w₁ , w₃) ⟩ Θ ⊢I (w , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w , Y)

    I-ID : ∀{Gr : Graph}{w : World}{Y : I-Form}
      → ⟨ Gr ⟩ [ (w , Y) ]L ⊢I (w , Y)

    I-Cut : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₂ w₁ : World}{X Z : I-Form}
      → ⟨ Gr ⟩ Θ₂ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₁ ::L (w₂ , X)) ⊢I (w₁ , Z)
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ⊢I (w₁ , Z)

    I-WK : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ ::L (w₂ , X)) ⊢I (w₁ , Y)

    I-CR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ (Θ ::L (w₂ , X) ::L (w₂ , X)) ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ ::L (w₂ , X)) ⊢I (w₁ , Y)

    I-EX : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₁ w₂ w : World}{X Y Z : I-Form}
      → ⟨ Gr ⟩ ((Θ₁ ::L (w₂ , Y) ::L (w₁ , X)) ++L Θ₂) ⊢I (w , Z)
      → ⟨ Gr ⟩ ((Θ₁ ::L (w₁ , X) ::L (w₂ , Y)) ++L Θ₂) ⊢I (w , Z)

    I-ML : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ w : World}{X Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (Θ ::L (w₁ , X) ::L (w₂ , X)) ⊢I (w , Y)
      → ⟨ Gr ⟩ ((Θ ::L (w₁ , X))) ⊢I (w , Y)

    I-MR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{Y : I-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ ⊢I (w₂ , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)

    I-TL : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ ::L (w₂ , One)) ⊢I (w₁ , Y)

    I-TR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w , One)

    I-PL : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y Z : I-Form}
      → ⟨ Gr ⟩ (Θ ::L (w₁ , X) ::L (w₁ , Y)) ⊢I (w₂ , Z)
      → ⟨ Gr ⟩ (Θ ::L (w₁ , X × Y)) ⊢I (w₂ , Z)

    I-PR : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w : World}{X Y : I-Form}
      → ⟨ Gr ⟩ Θ₁ ⊢I (w , X)
      → ⟨ Gr ⟩ Θ₂ ⊢I (w , Y)
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ⊢I (w , X × Y)

    I-IL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₁ w₂ w : World}{X Y Z : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Θ₂ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₁ ::L (w₂ , Y)) ⊢I (w , Z)
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂ ::L (w₁ , X ⇒ Y)) ⊢I (w , Z)

    I-IR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInICtx w₂ Θ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::L (w₁ , w₂) ⟩ (Θ ::L (w₂ , X)) ⊢I (w₂ , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , X ⇒ Y)

    I-GR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ [] ⊢LL [ (w , A) ]R ∣ []
      → ⟨ Gr ⟩ Θ ⊢I (w , (G A)) 

  -- Co-intuitionistic fragment of BiLNL logic:
  data ⟨_⟩_⊢C_ : Graph → (World ∧ C-Form) → C-Ctx → Set where
    C-RL : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → ⟨ Gr ::L (w₁ , w₁) ⟩ (w₂ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₂ , S) ⊢C Ψ

    C-TS : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ w₃ w : World}{S : C-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr ::L (w₁ , w₃) ⟩ (w , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w , S) ⊢C Ψ

    C-ID : ∀{Gr : Graph}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ (w , S) ⊢C [ (w , S) ]R

    C-Cut : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::R Ψ₂)
      → ⟨ Gr ⟩ (w₂ , T) ⊢C Ψ₁      
      → ⟨ Gr ⟩ (w₁ , S) ⊢C (Ψ₁ ++R Ψ₂)

    C-WK : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::R Ψ)

    C-CR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::R (w₂ , T) ::R Ψ)
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , T) ::R Ψ)

    C-EX : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ w : World}{R S T : C-Form}
      → ⟨ Gr ⟩ (w , R) ⊢C (Ψ₁ ++R (w₁ , S) ::R (w₂ , T) ::R Ψ₂)
      → ⟨ Gr ⟩ (w , R) ⊢C (Ψ₁ ++R (w₂ , T) ::R (w₁ , S) ::R Ψ₂)

    C-ML : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (w₂ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₁ , S) ⊢C Ψ

    C-MR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ w : World}{S T : C-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ (w , S) ⊢C ((w₂ , T) ::R (w₁ , T) ::R Ψ)
      → ⟨ Gr ⟩ (w , S) ⊢C ((w₁ , T) ::R Ψ)

    C-FL : ∀{Gr : Graph}{Ψ : C-Ctx}{w : World}
      → ⟨ Gr ⟩ (w , Zero) ⊢C Ψ

    C-FR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → ⟨ Gr ⟩ (w₁ , S) ⊢C Ψ
      → ⟨ Gr ⟩ (w₁ , S) ⊢C ((w₂ , Zero) ::R Ψ)

    C-DL : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{S T : C-Form}
      → ⟨ Gr ⟩ (w , S) ⊢C Ψ₁
      → ⟨ Gr ⟩ (w , T) ⊢C Ψ₂
      → ⟨ Gr ⟩ (w , S + T) ⊢C (Ψ₁ ++R Ψ₂)

    C-DR : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{R S T : C-Form}
      → ⟨ Gr ⟩ (w₁ , R) ⊢C ((w₂ , S) ::R (w₂ , T) ::R Ψ)
      → ⟨ Gr ⟩ (w₁ , R) ⊢C ((w₂ , S + T) ::R Ψ)

    C-SL : ∀{Gr : Graph}{Ψ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInCCtx w₂ Ψ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::L (w₂ , w₁) ⟩ (w₂ , S) ⊢C ((w₂ , T) ::R Ψ)
      → ⟨ Gr ⟩ (w₁ , S ≺ T) ⊢C Ψ

    C-SR : ∀{Gr : Graph}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ w : World}{R S T : C-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ (w , R) ⊢C ((w₂ , S) ::R Ψ₂)
      → ⟨ Gr ⟩ (w₂ , T) ⊢C Ψ₁
      → ⟨ Gr ⟩ (w , R) ⊢C ((w₁ , S ≺ T) ::R Ψ₁ ++R Ψ₂)

    C-HL : ∀{Gr : Graph}{Ψ : C-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ [] ∣ [ (w , A) ]L ⊢LL [] ∣ Ψ
      → ⟨ Gr ⟩ (w , H A) ⊢C Ψ

  -- Linear Core of BiLNL logic:
  data ⟨_⟩_∣_⊢LL_∣_ : Graph → I-Ctx → BiL-LCtx → BiL-RCtx → C-Ctx → Set where
  -- Abstract Kripke Graph Rules:
    LL-RL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}
      → ⟨ Gr ::L (w , w) ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ

    LL-TS : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ w₃ : World}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr ::L (w₁ , w₃) ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ

    LL-ML : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{A : BiL-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Θ ∣ (Γ ::L (w₁ , A) ::L (w₂ , A)) ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ (Γ ::L (w₁ , A)) ⊢LL Δ ∣ Ψ

    LL-MR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{A : BiL-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL ((w₂ , A) ::R (w₁ , A) ::R Δ) ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL ((w₁ , A) ::R Δ) ∣ Ψ

    LL-IML : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{X : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (Θ ::L (w₁ , X) ::L (w₂ , X)) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ (Θ ::L (w₁ , X)) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-CMR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{S : C-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w₂ , S) ::R (w₁ , S) ::R Ψ)
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w₁ , S) ::R Ψ)

  -- Structural Rules:
    LL-WKL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{X : I-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ (Θ ::L (w , X)) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-WKR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w , S) ::R Ψ)

    LL-CTRL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{X : I-Form}
      → ⟨ Gr ⟩ (Θ ::L (w , X) ::L (w , X)) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ (Θ ::L (w , X)) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-CTRR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w , S) ::R (w , S) ::R Ψ)
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w , S) ::R Ψ)

    LL-EXL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{A B : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ ((Γ₁ ::L (w₁ , A) ::L (w₂ , B)) ++L Γ₂) ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ ((Γ₁ ::L (w₂ , B) ::L (w₁ , A)) ++L Γ₂) ⊢LL Δ ∣ Ψ

    LL-EXR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{A B : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL (Δ₁ ++R ((w₁ , A) ::R (w₂ , B) ::R Δ₂)) ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL (Δ₁ ++R ((w₂ , B) ::R (w₁ , A) ::R Δ₂)) ∣ Ψ

    LL-IEXL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ ((Θ₁ ::L (w₁ , X) ::L (w₂ , Y)) ++L Θ₂) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ ((Θ₁ ::L (w₂ , Y) ::L (w₁ , X)) ++L Θ₂) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-CEXR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ (Ψ₁ ++R ((w₁ , S) ::R (w₂ , T) ::R Ψ₂))
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ (Ψ₁ ++R ((w₂ , T) ::R (w₁ , S) ::R Ψ₂))

    LL-ID : ∀{Gr : Graph}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ [] ∣ [ (w , A) ]L ⊢LL [ (w , A) ]R ∣ []

    LL-Cut : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ Θ₁ ∣ Γ₂ ⊢LL ((w , A) ::R Δ₂) ∣ Ψ₁
      → ⟨ Gr ⟩ Θ₂ ∣ (Γ₁ ::L (w , A)) ⊢LL Δ₁ ∣ Ψ₂
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ∣ (Γ₁ ++L Γ₂) ⊢LL (Δ₁ ++R Δ₂) ∣ (Ψ₁ ++R Ψ₂)

    LL-ICut : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{X : I-Form}
      → ⟨ Gr ⟩ Θ₂ ⊢I (w , X)
      → ⟨ Gr ⟩ (Θ₁ ::L (w , X)) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-CCut : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w , S) ::R Ψ₂)
      → ⟨ Gr ⟩ (w , S) ⊢C Ψ₁
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ (Ψ₁ ++R Ψ₂)

  -- Conjunction and Tensor Rules:
    LL-IL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ (Γ ::L (w , True)) ⊢LL Δ ∣ Ψ

    LL-IR : ∀{Gr : Graph}{w : World}
      → ⟨ Gr ⟩ [] ∣ [] ⊢LL [ (w , True) ]R ∣ []

    LL-CL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{X Y : I-Form}
      → ⟨ Gr ⟩ ((Θ₁ ::L (w , X) ::L (w , Y)) ++L Θ₂) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ ((Θ₁ ::L (w , X × Y)) ++L Θ₂) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-TL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{A B : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ ((Γ₁ ::L (w , A) ::L (w , B)) ++L Γ₂) ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ ((Γ₁ ::L (w , A ⊗ B)) ++L Γ₂) ⊢LL Δ ∣ Ψ

    LL-TR : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{A B : BiL-Form}
      → ⟨ Gr ⟩ Θ₁ ∣ Γ₁ ⊢LL ((w , A) ::R Δ₁) ∣ Ψ₁
      → ⟨ Gr ⟩ Θ₂ ∣ Γ₂ ⊢LL ((w , B) ::R Δ₂) ∣ Ψ₂
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ∣ (Γ₁ ++L Γ₂) ⊢LL ((w , A ⊗ B) ::R (Δ₁ ++R Δ₂)) ∣ (Ψ₁ ++R Ψ₂)
      
  -- Disjunction and Par Rules
    LL-FLL : ∀{Gr : Graph}{w : World}
      → ⟨ Gr ⟩ [] ∣ [ (w , False) ]L ⊢LL [] ∣ []

    LL-FLR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL ((w , False) ::R Δ) ∣ Ψ

    LL-DR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{S T : C-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ (Ψ₁ ++R ((w , S) ::R (w , T) ::R Ψ₂))
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ (Ψ₁ ++R ((w , S + T) ::R Ψ₂))

    LL-PL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w : World}{A B : BiL-Form}
      → ⟨ Gr ⟩ Θ₁ ∣ (Γ₁ ::L (w , A)) ⊢LL Δ₁ ∣ Ψ₁
      → ⟨ Gr ⟩ Θ₂ ∣ (Γ₂ ::L (w , B)) ⊢LL Δ₂ ∣ Ψ₂
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ∣ ((Γ₁ ++L Γ₂) ::L (w , A ⊕ B)) ⊢LL (Δ₁ ++R Δ₂) ∣ (Ψ₁ ++R Ψ₂)

    LL-PR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{A B : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL (Δ₁ ++R ((w , A) ::R (w , B) ::R Δ₂)) ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL (Δ₁ ++R ((w , A ⊕ B) ::R Δ₂)) ∣ Ψ

    LL-ImpL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ : World}{A B : BiL-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Θ₁ ∣ Γ₁ ⊢LL ((w₂ , A) ::R Δ₁) ∣ Ψ₁
      → ⟨ Gr ⟩ Θ₂ ∣ (Γ₂ ::L (w₂ , B)) ⊢LL Δ₂ ∣ Ψ₂
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ∣ ((Γ₁ ++L Γ₂) ::L (w₁ , A ⊸ B)) ⊢LL (Δ₁ ++R Δ₂) ∣ (Ψ₁ ++R Ψ₂)

    LL-ImpR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{A B : BiL-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInICtx w₂ Θ) → ⊥)
      → ((worldInBiLLCtx w₂ Γ) → ⊥)
      → ((worldInBiLRCtx w₂ Δ) → ⊥)
      → ((worldInCCtx w₂ Ψ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::L (w₁ , w₂) ⟩ Θ ∣ (Γ ::L (w₂ , A)) ⊢LL ((w₂ , B) ::R Δ) ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL ((w₁ , A ⊸ B) ::R Δ) ∣ Ψ      

    LL-IImpL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Θ₁ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₂ ::L (w₂ , Y)) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ ((Θ₁ ++L Θ₂) ::L (w₁ , X ⇒ Y)) ∣ Γ ⊢LL Δ ∣ Ψ

  -- Co-implication Rules:
    LL-SL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w₁ w₂ : World}{A B : BiL-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInICtx w₂ Θ) → ⊥)
      → ((worldInBiLLCtx w₂ Γ) → ⊥)
      → ((worldInBiLRCtx w₂ Δ) → ⊥)
      → ((worldInCCtx w₂ Ψ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr ::L (w₂ , w₁) ⟩ Θ ∣ (Γ ::L (w₂ , A)) ⊢LL ((w₂ , B) ::R Δ) ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ (Γ ::L (w₁ , A ≺L B)) ⊢LL Δ ∣ Ψ

    
    LL-SR : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{Γ₁ Γ₂ : BiL-LCtx}{Δ₁ Δ₂ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ : World}{A B : BiL-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ₁ ∣ Γ₁ ⊢LL ((w₂ , A) ::R Δ₁) ∣ Ψ₁
      → ⟨ Gr ⟩ Θ₂ ∣ (Γ₂ ::L (w₂ , B)) ⊢LL Δ₂ ∣ Ψ₂
      → ⟨ Gr ⟩ (Θ₁ ++L Θ₂) ∣ (Γ₁ ++L Γ₂) ⊢LL ((w₁ , A ≺L B) ::R (Δ₁ ++R Δ₂)) ∣ (Ψ₁ ++R Ψ₂)

    LL-CSR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ₁ Ψ₂ : C-Ctx}{w₁ w₂ : World}{S T : C-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w₂ , S) ::R Ψ₁)
      → ⟨ Gr ⟩ (w₂ , T) ⊢C Ψ₂
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w₁ , S ≺ T) ::R (Ψ₁ ++R Ψ₂))

  -- Adjoint Functors Rules
    LL-FL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{X : I-Form}
      → ⟨ Gr ⟩ (Θ ::L (w , X)) ∣ Γ ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ (Γ ::L (w , F X)) ⊢LL Δ ∣ Ψ

    LL-FR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{X : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w , X)
      → ⟨ Gr ⟩ Θ ∣ [] ⊢LL [ (w , F X) ]R ∣ []

    LL-JL : ∀{Gr : Graph}{Ψ : C-Ctx}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ (w , S) ⊢C Ψ
      → ⟨ Gr ⟩ [] ∣ [ (w , J S) ]L ⊢LL [] ∣ Ψ

    LL-JR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{S : C-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w , S) ::R Ψ)
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL ((w , J S) ::R Δ) ∣ Ψ

    LL-GL : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ (Γ ::L (w , A)) ⊢LL Δ ∣ Ψ
      → ⟨ Gr ⟩ (Θ ::L (w , G A)) ∣ Γ ⊢LL Δ ∣ Ψ

    LL-HR : ∀{Gr : Graph}{Θ : I-Ctx}{Γ : BiL-LCtx}{Δ : BiL-RCtx}{Ψ : C-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL ((w , A) ::R Δ) ∣ Ψ
      → ⟨ Gr ⟩ Θ ∣ Γ ⊢LL Δ ∣ ((w , H A) ::R Ψ)
