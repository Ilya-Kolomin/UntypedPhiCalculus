module UntypedPhiCalculus where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)

infix 6 _,_
infixr 5 _∪_
infix 4 _∋_
infix 4 _∣_⊢_

data Type : Set where
  ★ : Type

data Phi : Set where
  φ : Phi

data ∅ : Set where
  void : ∅

data _∪_ : Set → Set → Set where
  first_  : {A B : Set}
    → A
    ---
    → A ∪ B
  second_ : {A B : Set}
    → B
    ---
    → A ∪ B

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
    → (L ∪ Phi)
      -----------
    → L ∣ Γ ⊢ ★
  
  makeObject_ : ∀ {L Γ}
    → ((L ∪ Phi) → (L ∣ (Γ , ★) ⊢ ★))
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

data ExampleLabel : Set where
  x : ExampleLabel
  y : ExampleLabel
  z : ExampleLabel

exampleObjectImpl : ∀ {Γ} → ((ExampleLabel ∪ Phi) → (ExampleLabel ∣ (Γ , ★) ⊢ ★))
exampleObjectImpl (first x) = ρ 0
exampleObjectImpl (first y) = (ρ 0) ∙ (first x)
exampleObjectImpl (first z) = (ρ 0) ∙ (first y)
exampleObjectImpl (second φ) = ρ 0

exampleObject : ∀ {Γ} → ExampleLabel ∣ Γ ⊢ ★
exampleObject = makeObject exampleObjectImpl