module Lecture6 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

data Σ (A : Set) (B : A → Set) : Set where
    ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B


data even : ℕ → Set
data odd  : ℕ → Set

data even where
    even-zero : even zero
    even-suc : ∀ {n : ℕ} → odd n  → even (suc n)

data odd where
    odd-suc : ∀ { n : ℕ } → even n → odd (suc n)

odd-∃ : ∀ { n } → odd n → ∃[ m ] ( 1 + m * 2 ≡ n )

even-∃ : ∀ { n } →  even n →  ∃[ m ] ( m * 2 ≡ n )
even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc n-1) with odd-∃ n-1
... | ⟨ x , refl ⟩ =  ⟨  suc x  , refl ⟩

odd-∃ (odd-suc n-1) with even-∃ n-1
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩
