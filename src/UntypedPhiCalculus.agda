module UntypedPhiCalculus where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

infixl 6 _,_
infix 4 _∋_
infix 4 _∣_⊢_
infix 7 _[_↦_]
infix 2 _⟿_
infixl 4 _∙_


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
  w : ExampleLabel

exampleObjectImpl : ∀ {Γ} → ((ExampleLabel ⊎ Phi) → ((ExampleLabel ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅))
exampleObjectImpl (inj₁ x) = inj₁ (ρ 0)
exampleObjectImpl (inj₁ y) = inj₁ ((ρ 0) ∙ (inj₁ x))
exampleObjectImpl (inj₁ z) = inj₁ emptyObj
exampleObjectImpl (inj₁ w) = inj₁ emptyObj
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

_[_] : ∀ {L Γ A B}
        → L ∣ Γ , B ⊢ A
        → L ∣ Γ ⊢ B
          ---------
        → L ∣ Γ ⊢ A
_[_] {L} {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N


-- reduction

app_helper : ∀ {L Γ} 
  (N : (L ⊎ Phi) → ((L ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅))
  (c : L)
  (u : L ∣ Γ , ★ ⊢ ★)
  ------------
  → ((L ⊎ Phi) → ((L ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅))
app_helper {L} {Γ} N c u = appN where
  appN : (L ⊎ Phi) → ((L ∣ (Γ , ★) ⊢ ★) ⊎ None ⊎ ∅)
  appN (inj₁ c) = inj₁ u
  appN = N

data _⟿_ : ∀ {L Γ A} → (L ∣ Γ ⊢ A) → (L ∣ Γ ⊢ A) → Set where

  congDOT : ∀ {L Γ} {M M′ : L ∣ Γ ⊢ ★} {l : L}
    → M ⟿ M′
      ----------------
    → M ∙ (inj₁ l) ⟿ M′ ∙ (inj₁ l)

  congAPP₁ : ∀ {L Γ} {N N′ M : L ∣ Γ ⊢ ★} {l : L}
    → N ⟿ N′
      ----------------
    → N [ l ↦ M ] ⟿ N′ [ l ↦ M ]

  congAPP₂ : ∀ {L Γ} {N M M′ : L ∣ Γ ⊢ ★} {l : L}
    → M ⟿ M′
      ----------------
    → N [ l ↦ M ] ⟿ N [ l ↦ M′ ]
  
  DOT : ∀ {L Γ c N t_c}
    {t : L ∣ Γ ⊢ ★} 
    {_ : t ≡ makeObject N}
    {_ : N c ≡ inj₁ t_c}
    ------------------------
    → t ∙ c ⟿ t_c [ t ]

  DOTφ : ∀ {L Γ c N t_φ} 
    {t : L ∣ Γ ⊢ ★}
    {_ : t ≡ makeObject N}
    {_ : N (inj₁ c) ≡ inj₂ (inj₁ empty)}
    {_ : N (inj₂ φ) ≡ inj₁ t_φ}
    ----------------------
    → t ∙ (inj₁ c) ⟿ t ∙ (inj₂ φ) ∙ (inj₁ c)
  
  APP : ∀ {L Γ c N}
    {t : L ∣ Γ ⊢ ★}
    {_ : t ≡ makeObject N}
    {_ : N (inj₁ c) ≡ inj₂ (inj₂ void)}
    {u : L ∣ Γ ⊢ ★}
      -----------------------
    → t [ c ↦ u ] ⟿ makeObject (app_helper N c (rename S_ u))


infix  2 _⟿→_
infix  1 begin_
infixr 2 _⟿→⟨_⟩_
infix  3 _∎

data _⟿→_ : ∀ {L Γ A} → (L ∣ Γ ⊢ A) → (L ∣ Γ ⊢ A) → Set where

  _∎ : ∀ {L Γ A} (M : L ∣ Γ ⊢ A)
      --------
    → M ⟿→ M

  _⟿→⟨_⟩_ : ∀ {L Γ A} (K : L ∣ Γ ⊢ A) {M N : L ∣ Γ ⊢ A}
    → K ⟿ M
    → M ⟿→ N
      ---------
    → K ⟿→ N

begin_ : ∀ {L} {Γ} {A} {M N : L ∣ Γ ⊢ A}
  → M ⟿→ N
    ------
  → M ⟿→ N
begin M⟿⋆N = M⟿⋆N

leftPart : ExampleLabel ∣ none ⊢ ★
leftPart = ((makeObject (\ { (inj₁ x) -> inj₁ (makeObject (\ {  (inj₁ y) -> inj₂ (inj₂ void) ; 
                                                                (inj₁ x) -> inj₂ (inj₁ empty) ;
                                                                (inj₁ z) -> inj₂ (inj₁ empty) ;
                                                                (inj₁ w) -> inj₂ (inj₁ empty) ;
                                                                (inj₂ φ) -> inj₂ (inj₁ empty)})) ; 
                              (inj₁ y) -> inj₂ (inj₁ empty) ;
                              (inj₁ z) -> inj₂ (inj₁ empty) ;
                              (inj₁ w) -> inj₂ (inj₁ empty) ;
                              (inj₂ φ) -> inj₂ (inj₁ empty)})) ∙ (inj₁ x))

firstStep : ExampleLabel ∣ none ⊢ ★
firstStep = leftPart [ y ↦ ((makeObject (\ {  (inj₁ z) -> (inj₁ emptyObj) ; -- empty object? in paper example there should be 'w', but it errors on something like (p 1)
                                              (inj₁ x) -> inj₂ (inj₁ empty) ;
                                              (inj₁ y) -> inj₂ (inj₁ empty) ;
                                              (inj₁ w) -> inj₂ (inj₁ empty) ;
                                              (inj₂ φ) -> inj₂ (inj₁ empty) })) ∙ (inj₁ z)) ]

secondStep : ExampleLabel ∣ none ⊢ ★
secondStep = leftPart [ y ↦ emptyObj ]

thirdStep : ExampleLabel ∣ none ⊢ ★
thirdStep = (makeObject (\ {  (inj₁ y) -> inj₂ (inj₂ void) ; 
                              (inj₁ x) -> inj₂ (inj₁ empty) ;
                              (inj₁ z) -> inj₂ (inj₁ empty) ;
                              (inj₁ w) -> inj₂ (inj₁ empty) ;
                              (inj₂ φ) -> inj₂ (inj₁ empty)})) [ y ↦ emptyObj ]

fourthStep : ExampleLabel ∣ none ⊢ ★
fourthStep = makeObject (\ {  (inj₁ y) -> inj₁ emptyObj ; 
                              (inj₁ x) -> inj₂ (inj₁ empty) ;
                              (inj₁ z) -> inj₂ (inj₁ empty) ;
                              (inj₁ w) -> inj₂ (inj₁ empty) ;
                              (inj₂ φ) -> inj₂ (inj₁ empty)})


_ : firstStep ⟿→ fourthStep
_ =
  begin
    firstStep
  ⟿→⟨ congAPP₂ DOT ⟩
    secondStep
  ⟿→⟨ congAPP₁ DOT ⟩
    thirdStep
  ⟿→⟨ APP ⟩
    fourthStep
  ∎