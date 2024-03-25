module Lecture5 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Function using (_∘_)

-- Typy i funkcje pomocnicze skopiowane z poprzednich wykładów:
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ {x : A} → from (to x) ≡ x
    to∘from : ∀ {y : B} → to (from y) ≡ y
open _≃_

postulate extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
postulate ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g


-- Tu zaczyna się wykład:

data −_ : Set → Set₁ where
  neg : ∀ { A }→ ( A → ⊥ ) → − A


¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A →  A → ⊥
¬-elim f a =  f a

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A -- ( (A → ⊥) → ⊥ )
¬¬-intro a = λ f → f a

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim f a = f (λ z → z a) -- f (¬¬-intro a) -- (¬-elim f) ( ¬¬-intro a )


contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b = λ z → ¬b (f z) -- ¬b ∘ f

data _<_ : ℕ → ℕ → Set where
  0<s : ∀ { n } → 0 < suc n
  s<s : ∀ { m n } → m < n → suc m < suc n

_ : ¬ ( 2 < 0 )
_ = λ ()

lemma : ∀ {m n} → suc m < suc n → m < n
lemma (s<s p) =  p

1notlessthan0 : ¬ (1 < 0)
1notlessthan0 = λ ()

_ : ¬ ( 2 < 1 )
_ =  (contraposition lemma) 1notlessthan0 -- ¬ ( m < n ) → ¬ ( suc m < suc n )


nonrefl : ∀ { n } → ¬ (n < n)
nonrefl {zero} = λ ()
nonrefl {suc n} =  contraposition lemma (nonrefl {n})
