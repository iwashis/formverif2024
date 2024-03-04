module lecture1 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + m = m
(succ m) + n = succ (m + n)

theorem₁ : 1 + 1 ≡ 2
theorem₁ = begin (1 + 1)
  ≡⟨⟩ ((succ zero) + 1)
  ≡⟨⟩ succ( zero + 1 )
  ≡⟨⟩ succ ( 1 )
  ≡⟨⟩ 2 ∎


r-neutrality-zero : ∀ (m : ℕ) → m + zero ≡ m
r-neutrality-zero zero = refl
r-neutrality-zero (succ m) = begin (succ m) + zero
  ≡⟨⟩ succ ( m + zero )
  ≡⟨ cong succ (r-neutrality-zero m) ⟩ succ m ∎


infixr 5 _+_
infixr 6 _·_

_·_ : ℕ → ℕ → ℕ
zero · m =  zero
(succ m) · n = m · n + n

_ : (2 · 3 + 1) ≡ 7
_ = refl

t = 2 · 3 + 1

·-right-zero : ∀ ( m : ℕ ) → m · zero ≡ zero
·-right-zero zero = refl
·-right-zero (succ m) = begin ( (succ m) · zero )
  ≡⟨⟩ ( m · zero ) + zero
  ≡⟨ r-neutrality-zero ( m · zero ) ⟩ m · zero
  ≡⟨ ·-right-zero m ⟩ zero ∎

+-assoc : ∀ ( m n p : ℕ ) → ( m + n ) + p ≡ m + ( n + p )
+-assoc zero n p = refl
+-assoc (succ m) n p = begin (( (succ m ) + n ) + p )
  ≡⟨⟩ ( succ ( m + n ) + p )
  ≡⟨⟩ succ ( ( m + n ) + p)
  ≡⟨ cong succ ( +-assoc m n p) ⟩ succ ( m + (n + p) )
  ≡⟨⟩ (succ m ) + (n + p) ∎

data List (A : Set) : Set where
  Nil : List A
  _⨾_ : A → List A → List A


_++_ : ∀ { A : Set } → List A → List A → List A
Nil ++ list2 = list2
(x ⨾ list1) ++ list2 = x ⨾ ( list1 ++ list2 )

nil-right-neutrality : ∀ { A : Set } ( list : List A ) → list ++ Nil ≡ list
nil-right-neutrality {A} Nil = refl
nil-right-neutrality {A} (x ⨾ list) = begin ( x ⨾ list  ) ++ Nil
  ≡⟨⟩ x ⨾ (list ++ Nil)
  ≡⟨ cong ( λ l → x ⨾ l ) ( nil-right-neutrality list) ⟩ x ⨾ list ∎
