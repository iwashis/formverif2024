module Lecture45 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B


proj₁ : ∀ {A B : Set}
    → A × B
    -----
    → A
proj₁ ⟨ x , y ⟩ = x
proj₂ : ∀ {A B : Set}
    → A × B
    -----
    → B
proj₂ ⟨ x , y ⟩ = y


data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ⊥ : Set where

⊥-elim : ∀ {A : Set } → ⊥ → A
⊥-elim = λ ()

data ¬_ ( A : Set ) : Set where
  neg : ( A → ⊥ ) → ¬ A

_ : ¬ ( 2 ≡ 3 )
_ = neg (λ ())

-- z poprzedniego wykładu --
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ {x : A} → from (to x) ≡ x
    to∘from : ∀ {y : B} → to (from y) ≡ y
open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =  record { to = λ x → x; from = λ y → y; from∘to = refl ; to∘from = refl }
≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record { to = from A≃B ; from = to A≃B ; from∘to = to∘from A≃B ; to∘from = from∘to A≃B   }



-- ćwiczenia --
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record { to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ; -- λ x →  ⟨ proj₂ x , proj₁ x ⟩ ;
                from =  λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
                from∘to = λ { { ⟨ x , y ⟩ } → refl  } ;
                to∘from = λ { { ⟨ x , y ⟩ } → refl  } }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record { to =  λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ } ;
                   from = λ { ⟨  x , ⟨ y  , z ⟩ ⟩ → ⟨ ⟨ x ,  y ⟩ , z  ⟩ }  ;
                   from∘to = λ { { ⟨ ⟨ x , y ⟩ , z ⟩ } → refl };
                   to∘from = λ { { ⟨  x , ⟨ y , z ⟩ ⟩ } → refl } }

data ⊤ : Set where
  tt : ⊤

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record { to = λ { ⟨ tt , x ⟩ → x } ;
                      from = ⟨_,_⟩ tt  ;
                      from∘to =  λ { { ⟨ tt , x ⟩ } → refl  } ;
                      to∘from = refl }
-- ⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A


case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ a) =  f a
case-⊎ f g (inj₂ b) =  g b
