module Lecture7 where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)



data _≤_ : ℕ → ℕ → Set where
 0≤n : ∀ { n } → zero ≤ n
 s≤s : forall { m n } → m ≤ n → suc m ≤ suc n

_≤?_ : ℕ → ℕ → Bool
zero ≤? n =  true
suc m ≤? zero =  false
suc m ≤? suc n =  m ≤? n


T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ false = λ ()
T→≡ true = λ _ → refl


≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt


≤?→≤ : ∀ { m n } → T ( m ≤? n ) → m ≤ n
≤?→≤ {zero} {n} tt = 0≤n
≤?→≤ {suc m} {suc n} p = s≤s (≤?→≤ p)

≤→≤? : ∀ { m n } → m ≤ n → T ( m ≤? n )
≤→≤? {zero} {n} 0≤n = tt
≤→≤? {suc m} {suc n} (s≤s p) = ≤→≤? p
