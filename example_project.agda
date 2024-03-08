module example_project where


-- W tym projekcie formalizujemy prosty język zdefiniowany w
-- https://groups.seas.harvard.edu/courses/cs152/2019sp/lectures/lec02-smallstep.pdf
-- wraz z jego semantyką small-step.

open import Data.String.Base using (String)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


Var : Set
Var = ℕ
-- Definiujemy składnię naszego języka:
data Exp : Set where
  var   : Var → Exp
  int   : ℕ → Exp
  _≔_⨾_ : Var → Exp → Exp → Exp
  _⊗_   : Exp → Exp → Exp
  _⊕_   : Exp → Exp → Exp


-- Przykładowe wyrażenie typu Exp:
foo = 1

example₁ : Exp
example₁ = foo ≔ ( int 6 ) ⨾ (((int 7) ⊗ (int 8)) ⊕ (var foo))



-- Small-step semantics--
data Cntxt : Set where
  Ø : Cntxt
  _⇉_,_ : Var → ℕ → Cntxt → Cntxt

_++_ : Cntxt → Cntxt → Cntxt
Ø ++ σ = σ
(x ⇉ n , σ) ++ τ = x ⇉ n , (σ ++ τ)

_⟦_≔_⟧ : Cntxt → Var → ℕ → Cntxt
σ ⟦ x ≔ n ⟧ = x ⇉ n , σ
Config : Set
Config = Cntxt × Exp

data _↘_ : Config → Config → Set where
  perm_as : ∀ { τ σ : Cntxt } → ∀ { e : Exp }
            ------------------------------------------------------
            → ⟨ τ ++ σ , e ⟩ ↘ ⟨ σ ++ τ , e ⟩

  var_red : ∀ { x : Var } → ∀ { n } → ∀ { σ : Cntxt }
            ------------------------------------------------------
            → ⟨ (x ⇉ n , σ)  , var x  ⟩ ↘  ⟨ σ  , int n ⟩

  left_add : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            → ⟨ σ , e ⊕ f ⟩ ↘ ⟨ σ' , e' ⊕ f ⟩

  right_add : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            → ⟨ σ , f ⊕ e ⟩ ↘ ⟨ σ' , f ⊕ e' ⟩

  add : ∀ { σ : Cntxt } → ∀ { m n }
            → ⟨ σ , (int m) ⊕ (int n) ⟩ ↘ ⟨ σ , int ( m + n ) ⟩

  left_mul : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            → ⟨ σ , e ⊗ f ⟩ ↘ ⟨ σ' , e' ⊗ f ⟩

  right_mul : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            → ⟨ σ , f ⊗ e ⟩ ↘ ⟨ σ' , f ⊗ e' ⟩

  mul : ∀ { σ : Cntxt } → ∀ { m n }
            → ⟨ σ , (int m) ⊗ (int n) ⟩ ↘ ⟨ σ , int ( m * n ) ⟩

  asg : ∀ { σ σ' : Cntxt } → ∀ { x : Var } → ∀ { n : ℕ } → ∀ { e₁ e₁' e₂ }
            → ⟨ σ , e₁ ⟩ ↘ ⟨ σ' , e₁' ⟩
            → ⟨ σ , (x ≔ e₁ ⨾ e₂) ⟩ ↘ ⟨ σ' , (x ≔ e₁' ⨾ e₂) ⟩

  asg_int : ∀ { σ : Cntxt } → ∀ { x : Var } → ∀ { n : ℕ } → ∀ { e }
            → ⟨ σ , x ≔ (int n) ⨾ e ⟩ ↘ ⟨ σ ⟦ x ≔ n ⟧ , e ⟩

data _↣_ : Config → Config → Set where
  take : ∀ { c c' } → c ↘ c' → c ↣ c'
  _andThen_ : ∀ {c c' c'' } → (c ↣ c') → (c' ↣ c'') → (c ↣ c'')

infixr 6 _andThen_

-- Przypomnijmy sobie nasze wyrażenie:
-- example₁ = foo ≔ ( int 6 ) ⨾ (((int 7) ⊗ (int 8)) ⊕ (var foo))
first_step : ⟨ Ø , example₁ ⟩ ↘ ⟨ ( foo ⇉ 6 , Ø ) , ((int 7) ⊗ (int 8)) ⊕ (var foo) ⟩
first_step = asg_int


_ : ⟨ Ø , example₁ ⟩ ↣ ⟨  Ø  ,( (int 7) ⊗ (int 8) ) ⊕ (int 6) ⟩
_ = (take first_step) andThen take right var_red add
