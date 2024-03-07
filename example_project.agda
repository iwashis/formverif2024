module example_project where


-- W tym projekcie formalizujemy prosty język zdefiniowany w
-- https://groups.seas.harvard.edu/courses/cs152/2019sp/lectures/lec02-smallstep.pdf
-- wraz z jego semantyką small-step.

open import Data.String.Base using (String)
open import Data.Nat.Base using (ℕ)
open import Data.Maybe using (Maybe; nothing; just)
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
example_program₁ = ("foo") ≔ ( int 6 ) ⨾ (((int 7) ⊗ (int 8)) ⊕ (var "foo"))



-- Under construction --
data Cntxt : Set where
  Ø : Cntxt
  _⇉_,_ : Var → ℕ → Cntxt → Cntxt

_++_ : Cntxt → Cntxt → Cntxt
Ø ++ σ = σ
(x ⇉ n , σ) ++ τ = x ⇉ n , (σ ++ τ)

Config : Set
Config = Cntxt × Exp

data _↘_ : Config → Config → Set where
  perm_as : ∀ { τ σ : Cntxt } → ∀ { e : Exp }
            ------------------------------------------------------
            → ⟨ τ ++ σ , e ⟩ ↘ ⟨ σ ++ τ , e ⟩

  var_red : ∀ { x : Var } → ∀ { n } → ∀ { σ : Cntxt }
            ------------------------------------------------------
            → ⟨ (x ⇉ n , σ)  , var x  ⟩ ↘  ⟨  σ , int n ⟩ -- ⟨ (x ⇉ n , σ)  , int n ⟩

  left_add : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            → ⟨ σ , e ⊕ f ⟩ ↘ ⟨ σ' , e' ⊕ f ⟩

  right_add : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            → ⟨ σ , f ⊕ e ⟩ ↘ ⟨ σ' , f ⊕ e' ⟩
