module Lecture5 where

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
