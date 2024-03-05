module example_project where


-- W tym projekcie formalizujemy prosty język zdefiniowany w
-- https://groups.seas.harvard.edu/courses/cs152/2019sp/lectures/lec02-smallstep.pdf
-- wraz z jego semantyką small-step.

open import Data.String.Base using (String)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


Var : Set
Var = String
-- Definiujemy składnię naszego języka:
data Exp : Set where
  var   : Var → Exp
  int   : ℕ → Exp
  _≔_⨾_ : String → Exp → Exp → Exp
  _⊗_   : Exp → Exp → Exp
  _⊕_   : Exp → Exp → Exp


-- Przykładowe wyrażenie typu Exp:
example_program₁ : Exp
example_program₁ = ("foo") ≔ ( int 6 ) ⨾ ( ((int 7) ⊗ (int 8)) ⊕ (var "foo") )



-- Under construction --
Store : Set
Store = Var → ℕ

Config : Set
Config = Exp × Store

data _◂_ : Config → Config → Set where
  var_reduc : ∀ { x : Var } → ∀ { σ : Store } → ⟨ var x , σ ⟩ ◂ ⟨ int (σ x) , σ ⟩
