module UntypedPhiCalculus where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

infix 6 _,_
infix 4 _∋_
infix 4 _∣_⊢_

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