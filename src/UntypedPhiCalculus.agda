module UntypedPhiCalculus where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

infix 6 _,_
infix 4 _∋_
infix 4 _∣_⊢_
infix 7 _[_↦_]

data Type : Set where
  ★ : Type

data Phi : Set where
  φ : Phi

data ∅ : Set where
  void : ∅

data None : Set where
  empty : None

data Parent : Set where
  none   : Parent
  _,_ : Parent → Type → Parent

data _∋_ : Parent → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → (Γ , A) ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      --------
    → (Γ , B) ∋ A

data _∣_⊢_ : Set → Parent → Type → Set where

  `_ : ∀ {L Γ A} 
    → Γ ∋ A
      --------
    → L ∣ Γ ⊢ A
  
  _∙_ : ∀ {L Γ}
    → L ∣ Γ ⊢ ★
    → (L ⊎ Phi)
      -----------
    → L ∣ Γ ⊢ ★
  
  makeObject_ : ∀ {L Γ}
    → ((L ⊎ Phi) → ((L ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅))
      --------------------------------------
    → L ∣ Γ ⊢ ★
     
  _[_↦_] : ∀ {L Γ}
    → L ∣ Γ ⊢ ★
    → L
    → L ∣ Γ ⊢ ★
      ------------
    → L ∣ Γ ⊢ ★

count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero     =  Z
count {Γ , ★} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

ρ_ : ∀ {L Γ} → ℕ → L ∣ Γ ⊢ ★
ρ n  =  ` count n

emptyObjImpl : ∀ {L Γ} → ((L ⊎ Phi) → ((L ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅))
emptyObjImpl _ = inj₂ (inj₁ empty)

emptyObj : ∀ {L Γ} → L ∣ Γ ⊢ ★
emptyObj = makeObject emptyObjImpl

data ExampleLabel : Set where
  x : ExampleLabel
  y : ExampleLabel
  z : ExampleLabel

exampleObjectImpl : ∀ {Γ} → ((ExampleLabel ⊎ Phi) → ((ExampleLabel ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅))
exampleObjectImpl (inj₁ x) = inj₁ (ρ 0)
exampleObjectImpl (inj₁ y) = inj₁ ((ρ 0) ∙ (inj₁ x))
exampleObjectImpl (inj₁ z) = inj₁ emptyObj
exampleObjectImpl (inj₂ φ) = inj₂ (inj₂ void)

exampleObject : ∀ {Γ} → ExampleLabel ∣ Γ ⊢ ★
exampleObject = makeObject exampleObjectImpl

-- renaming
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → (Γ , B) ∋ A → (Δ , B) ∋ A)
ext p Z      =  Z
ext p (S a)  =  S (p a)

{-# TERMINATING #-}
rename : ∀ {Γ Δ L}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → L ∣ Γ ⊢ A → L ∣ Δ ⊢ A)
rename p (` a)          =  ` (p a)
rename p (N ∙ l)        =  (rename p N) ∙ l
rename p (N [ a ↦ M ])  =  (rename p N) [ a ↦ (rename p M) ]
rename {Γ} {Δ} {L} p (makeObject N) = makeObject renamedN where
  case_term : (L ∣ Γ , ★ ⊢ ★) → (L ∣ Δ , ★ ⊢ ★ ⊎ None ⊎ ∅)
  case_term term = inj₁ (rename (ext p) term)
  
  renamedN : (L ⊎ Phi) → (L ∣ Δ , ★ ⊢ ★ ⊎ None ⊎ ∅)
  renamedN l = [ case_term , inj₂ ]′ (N l)

 -- simultaneous substitution
exts : ∀ {Γ Δ L} → (∀ {A} → Γ ∋ A → L ∣ Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → L ∣ Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S a)  =  rename S_ (σ a)

{-# TERMINATING #-}
subst : ∀ {Γ Δ L}
  → (∀ {A} → Γ ∋ A → L ∣ Δ ⊢ A)
    ------------------------
  → (∀ {A} → L ∣ Γ ⊢ A → L ∣ Δ ⊢ A)
subst σ (` k)          =  σ k
subst p (N ∙ l)        =  (subst p N) ∙ l
subst p (N [ a ↦ M ])  =  (subst p N) [ a ↦ (subst p M) ]
subst {Γ} {Δ} {L} p (makeObject N) = makeObject substN where
  case_term : (L ∣ Γ , ★ ⊢ ★) → (L ∣ Δ , ★ ⊢ ★ ⊎ None ⊎ ∅)
  case_term term = inj₁ (subst (exts p) term)
  
  substN : (L ⊎ Phi) → (L ∣ Δ , ★ ⊢ ★ ⊎ None ⊎ ∅)
  substN l = [ case_term , inj₂ ]′ (N l)

subst-zero : ∀ {Γ B L} → (L ∣ Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (L ∣ Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S a)  =  ` a

