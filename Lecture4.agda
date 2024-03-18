module Lecture4 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

f : ℕ → ℕ
f = λ { zero → suc (zero) ; (suc n) → n }

postulate extensionality : ∀ {A B : Set} {f g : A → B}
                → (∀ (x : A) → f x ≡ g x)
                  -----------------------
                → f ≡ g

_∘_ : ∀ { A  B C : Set } → (B → C) → (A → B) → ( A → C )
g ∘ f = λ x → g ( f x  )

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)


same-app' : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app' m zero rewrite +-comm m zero = refl
same-app' m (suc n) rewrite +-comm m (suc n) = {!!}


same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ ( m n : ℕ ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n)  = cong suc (helper m n)

same : _+′_ ≡ _+_
same =  extensionality ( λ x → extensionality ( λ y → same-app x y ) )

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
--
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans AB BC = record { to = (to BC) ∘ (to AB) ;
                        from = (from AB) ∘ (from BC) ;
                        from∘to = λ { x } → {!!} ;
                        to∘from = {!!} }

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

data FakeBool : Set where
  tt : FakeBool
  ff : FakeBool

_ : FakeBool ≲ ℕ
_  = record { to = λ { tt → 0 ; ff → 1 } ;
              from = λ { zero → tt ; ( suc n ) → ff };
              from∘to = λ { tt → refl ; ff → refl } }
≲-refl : ∀ { A } →  A ≲ A
≲-refl = record { to = λ z → z ; from = λ z → z ; from∘to = λ _ → refl }
