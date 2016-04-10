module BiLNL where

open import nat renaming (_+_ to _+ℕ_)
open import snoc
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

mutual 
  data I-Form : Set where
    True : I-Form
    _×_ : I-Form → I-Form → I-Form
    _⇒_ : I-Form → I-Form → I-Form
    G   : BiL-Form → I-Form

  data C-Form : Set where
    False : C-Form
    _+_ : C-Form → C-Form → C-Form
    _-_ : C-Form → C-Form → C-Form

  data BiL-Form : Set where
    I : BiL-Form
    J : BiL-Form
    _⊗_ : BiL-Form → BiL-Form → BiL-Form
    _⊕_ : BiL-Form → BiL-Form → BiL-Form
    _⊸_ : BiL-Form → BiL-Form → BiL-Form
    _≻L_ : BiL-Form → BiL-Form → BiL-Form
    
I-Ctx : Set
I-Ctx = Snoc (World ∧ I-Form)

worldInICtx : World → I-Ctx → Set
worldInICtx = inPairSnocFst _=ℕ_

C-Ctx : Set
C-Ctx = Snoc (World ∧ C-Form)

worldInCCtx : World → C-Ctx → Set
worldInCCtx = inPairSnocFst _=ℕ_

BiL-Ctx : Set
BiL-Ctx = Snoc (World ∧ BiL-Form)

worldInBiLCtx : World → BiL-Ctx → Set
worldInBiLCtx = inPairSnocFst _=ℕ_

mutual
  data ⟨_⟩_⊢I_ : Graph → I-Ctx → (World ∧ I-Form) → Set where
    I-RL : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{Y : I-Form}
      → ⟨ Gr :: (w , w) ⟩ Θ ⊢I (w , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w , Y)

    I-TS : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ w₃ w : World}{Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → w₂ ⟨ Gr ⟩ w₃
      → ⟨ Gr :: (w₁ , w₃) ⟩ Θ ⊢I (w , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w , Y)

    I-ID : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{Y : I-Form}
      → ⟨ Gr ⟩ [ (w , Y) ] ⊢I (w , Y)

    I-Cut : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₂ w₁ : World}{X Z : I-Form}
      → ⟨ Gr ⟩ Θ₂ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₁ :: (w₂ , X)) ⊢I (w₁ , Z)
      → ⟨ Gr ⟩ (Θ₁ ++ Θ₂) ⊢I (w₁ , Z)

    I-WK : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ :: (w₂ , X)) ⊢I (w₁ , Y)

    I-CR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ⟨ Gr ⟩ (Θ :: (w₂ , X) :: (w₂ , X)) ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ :: (w₂ , X)) ⊢I (w₁ , Y)

    I-EX : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₁ w₂ w : World}{X Y Z : I-Form}
      → ⟨ Gr ⟩ ((Θ₁ :: (w₂ , Y) :: (w₁ , X)) ++ Θ₂) ⊢I (w , Z)
      → ⟨ Gr ⟩ ((Θ₁ :: (w₁ , X) :: (w₂ , Y)) ++ Θ₂) ⊢I (w , Z)

    I-ML : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ w : World}{X Y : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ (Θ :: (w₁ , X) :: (w₂ , X)) ⊢I (w , Y)
      → ⟨ Gr ⟩ ((Θ :: (w₁ , X))) ⊢I (w , Y)

    I-MR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{Y : I-Form}
      → w₂ ⟨ Gr ⟩ w₁
      → ⟨ Gr ⟩ Θ ⊢I (w₂ , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)

    I-TL : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , Y)
      → ⟨ Gr ⟩ (Θ :: (w₂ , True)) ⊢I (w₁ , Y)

    I-TR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{Y : I-Form}
      → ⟨ Gr ⟩ Θ ⊢I (w , True)

    I-PL : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y Z : I-Form}
      → ⟨ Gr ⟩ (Θ :: (w₁ , X) :: (w₁ , Y)) ⊢I (w₂ , Z)
      → ⟨ Gr ⟩ (Θ :: (w₁ , X × Y)) ⊢I (w₂ , Z)

    I-PR : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w : World}{X Y : I-Form}
      → ⟨ Gr ⟩ Θ₁ ⊢I (w , X)
      → ⟨ Gr ⟩ Θ₂ ⊢I (w , Y)
      → ⟨ Gr ⟩ (Θ₁ ++ Θ₂) ⊢I (w , X × Y)

    I-IL : ∀{Gr : Graph}{Θ₁ Θ₂ : I-Ctx}{w₁ w₂ w : World}{X Y Z : I-Form}
      → w₁ ⟨ Gr ⟩ w₂
      → ⟨ Gr ⟩ Θ₂ ⊢I (w₂ , X)
      → ⟨ Gr ⟩ (Θ₁ :: (w₂ , Y)) ⊢I (w , Z)
      → ⟨ Gr ⟩ (Θ₁ ++ Θ₂ :: (w₁ , X ⇒ Y)) ⊢I (w , Z)

    I-IR : ∀{Gr : Graph}{Θ : I-Ctx}{w₁ w₂ : World}{X Y : I-Form}
      → ((worldInGr w₂ Gr) → ⊥)
      → ((worldInICtx w₂ Θ) → ⊥)
      → ((w₁ =W w₂) → ⊥)
      → ⟨ Gr :: (w₁ , w₂) ⟩ (Θ :: (w₂ , X)) ⊢I (w₂ , Y)
      → ⟨ Gr ⟩ Θ ⊢I (w₁ , X ⇒ Y)

    I-GR : ∀{Gr : Graph}{Θ : I-Ctx}{w : World}{A : BiL-Form}
      → ⟨ Gr ⟩ Θ ∣ [] ⊢LL [ (w , A) ] ∣ []
      → ⟨ Gr ⟩ Θ ⊢I (w , (G A)) 
      

  data ⟨_⟩_⊢C_ : Graph → C-Ctx → C-Form → Set where

  data ⟨_⟩_∣_⊢LL_∣_ : Graph → I-Ctx → BiL-Ctx → BiL-Ctx → C-Ctx → Set where
