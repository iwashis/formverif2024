module example_project where


-- W tym projekcie formalizujemy prosty język zdefiniowany w
-- https://groups.seas.harvard.edu/courses/cs152/2019sp/lectures/lec02-smallstep.pdf
-- wraz z jego semantyką small-step.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.String.Base using (String)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)

-- wprowadzamy type alias Var
Var : Set
Var = ℕ
-- Definiujemy składnię naszego języka.
-- W klasycznym zapisie BNF, wyrażenia naszego języka definiujemy:
-- e := var x | int n | x ≔ n ⨾ e | e ⊕ e | e ⊗ e
-- Używając ADT, definicja typu reprezentującego wyrażenia naszego języka jest
-- następująca:
data Exp : Set where
  var   : Var → Exp
  int   : ℕ → Exp
  _≔_⨾_ : Var → Exp → Exp → Exp
  _⊗_   : Exp → Exp → Exp
  _⊕_   : Exp → Exp → Exp


-- na potrzeby przykładów wprowadzmy nazwe zmiennej (u nas zmienne są liczbami)
foo = 1
-- i zdefiniujmy przykładowe wyrażenie typu Exp:
example₁ : Exp
example₁ = foo ≔ ( int 6 ) ⨾ (((int 7) ⊗ (int 8)) ⊕ (var foo))

------------------------------------
--
-- Semantyki języka
--
------------------------------------

-- Żeby poprawnie zdefniować semantyki (big- i small- step semantics)
-- potrzebujemy wprowadzić typ reprezentujący pamięć obliczeń
-- (przechowującą wartości przypisań zmiennych)

-- Store/Cntxt, czyli teoretyczny model pamięci --
data Cntxt : Set where
  Ø : Cntxt
  _⇉_,_ : Var → ℕ → Cntxt → Cntxt

-- konkatenacja pamieci
_++_ : Cntxt → Cntxt → Cntxt
Ø ++ σ = σ
(x ⇉ n , σ) ++ τ = x ⇉ n , (σ ++ τ)

-- dorzucienie nowej komórki do pamięci
_⟦_≔_⟧ : Cntxt → Var → ℕ → Cntxt
σ ⟦ x ≔ n ⟧ = x ⇉ n , σ
Config : Set
Config = Cntxt × Exp

-- typ, dzięki ktoremu będziemy mieli pewność, że nie dorzucimy dwa razy tej samej
-- nazwy zmiennej
data _∉_ : Var → Cntxt → Set where
  x∉Ø : ∀ { x } → x ∉ Ø
  x∉σ : ∀ { x y } →  ∀ {σ } → ∀ { n } → ¬ (x ≡ y) → x ∉ σ → x ∉ ( y ⇉ n , σ )




-- Small-step semantics--
data _↘_ : Config → Config → Set where
  perm : ∀ { τ σ : Cntxt } → ∀ { e : Exp }
            ------------------------------------------------------
            → ⟨ τ ++ σ , e ⟩ ↘ ⟨ σ ++ τ , e ⟩

  varred : ∀ { x : Var } → ∀ { n } → ∀ { σ : Cntxt }
            ------------------------------------------------------
            → ⟨ (x ⇉ n , σ)  , var x  ⟩ ↘  ⟨ (x ⇉ n , σ )  , int n ⟩

  leftadd : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            ------------------------------------------------------
            → ⟨ σ , e ⊕ f ⟩ ↘ ⟨ σ' , e' ⊕ f ⟩

  rightadd : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            ------------------------------------------------------
            → ⟨ σ , f ⊕ e ⟩ ↘ ⟨ σ' , f ⊕ e' ⟩

  add : ∀ { σ : Cntxt } → ∀ { m n }
            ------------------------------------------------------
            → ⟨ σ , (int m) ⊕ (int n) ⟩ ↘ ⟨ σ , int ( m + n ) ⟩

  leftmul : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            ------------------------------------------------------
            → ⟨ σ , e ⊗ f ⟩ ↘ ⟨ σ' , e' ⊗ f ⟩

  rightmul : ∀ { σ σ' : Cntxt } → ∀ { e e' f : Exp }
            → ⟨ σ , e ⟩ ↘ ⟨ σ' , e' ⟩
            ------------------------------------------------------
            → ⟨ σ , f ⊗ e ⟩ ↘ ⟨ σ' , f ⊗ e' ⟩

  mul : ∀ { σ : Cntxt } → ∀ { m n }
            ------------------------------------------------------
            → ⟨ σ , (int m) ⊗ (int n) ⟩ ↘ ⟨ σ , int ( m * n ) ⟩

  asg : ∀ { σ σ' : Cntxt } → ∀ { x : Var } → ∀ { n : ℕ } → ∀ { e₁ e₁' e₂ }
            → ⟨ σ , e₁ ⟩ ↘ ⟨ σ' , e₁' ⟩
            ------------------------------------------------------
            → ⟨ σ , (x ≔ e₁ ⨾ e₂) ⟩ ↘ ⟨ σ' , (x ≔ e₁' ⨾ e₂) ⟩

  asgint : ∀ { σ : Cntxt } → ∀ { x : Var } → ∀ { n : ℕ } → ∀ { e }
            →  x ∉ σ
            ------------------------------------------------------
            → ⟨ σ , x ≔ (int n) ⨾ e ⟩ ↘ ⟨ σ ⟦ x ≔ n ⟧ , e ⟩

data _↣_ : Config → Config → Set where
  take : ∀ { c c' } → (c ↘ c') → (c ↣ c')
  _andThen_ : ∀ {c c' c'' } → (c ↣ c') → (c' ↣ c'') → (c ↣ c'')

infixr 6 _andThen_

-- Przypomnijmy sobie nasze wyrażenie:
-- example₁ = foo ≔ ( int 6 ) ⨾ (((int 7) ⊗ (int 8)) ⊕ (var foo))
first_step : ⟨ Ø , example₁ ⟩ ↘ ⟨ ( foo ⇉ 6 , Ø ) , ((int 7) ⊗ (int 8)) ⊕ (var foo) ⟩
first_step = asgint x∉Ø


_ : ⟨ Ø , example₁ ⟩ ↣ ⟨ ( foo ⇉ 6 , Ø )  , int 62 ⟩
_ = (take first_step) andThen
    take (rightadd varred) andThen
    take (leftadd mul) andThen
    take add


-- Big-step semantics

data _≡>_ : Config → Config → Set where
  perm : ∀ { τ σ : Cntxt } → ∀ { e } → ∀ { n : ℕ }
          → ⟨ τ ++ σ , e ⟩ ≡> ⟨ τ ++ σ , int n ⟩
            ------------------------------------------------------
          → ⟨ σ ++ τ , e ⟩ ≡> ⟨ σ ++ τ , int n ⟩

  varred : ∀ { x : Var } → ∀ { n } → ∀ { σ : Cntxt }
            ------------------------------------------------------
          → ⟨ (x ⇉ n , σ)  , var x  ⟩  ≡> ⟨ (x ⇉ n , σ )  , int n ⟩

  add : ∀ { σ σ' σ'' } → ∀ { n₁ n₂ } → ∀ { e₁ e₂ }
          → ⟨ σ   , e₁ ⟩      ≡> ⟨  σ'' , int n₁ ⟩
          → ⟨ σ'' , e₂ ⟩      ≡> ⟨  σ' , int n₂ ⟩
            ------------------------------------------------------
          → ⟨ σ   , e₁ ⊗ e₂ ⟩ ≡> ⟨  σ' , int( n₁ * n₂ ) ⟩

  mul : ∀ { σ σ' σ'' } → ∀ { n₁ n₂ } → ∀ { e₁ e₂ }
          → ⟨ σ   , e₁ ⟩      ≡> ⟨  σ'' , int n₁ ⟩
          → ⟨ σ'' , e₂ ⟩      ≡> ⟨  σ' , int n₂ ⟩
            ------------------------------------------------------
          → ⟨ σ   , e₁ ⊗ e₂ ⟩ ≡> ⟨  σ' , int( n₁ * n₂ ) ⟩

  asg : ∀ { σ σ' σ'' } → ∀ { n₁ n₂ } → ∀ { e₁ e₂ } → ∀ { x }
          → ⟨ σ   , e₁ ⟩            ≡> ⟨ σ'' , int n₁ ⟩
          → x ∉ σ'' -- tu musimy założyć, że z kontekstem σ'' jest wszystko ok
          → ⟨ σ'' ⟦ x ≔ n₁ ⟧ , e₂ ⟩ ≡> ⟨ σ' , int n₂ ⟩
            ------------------------------------------------------
          → ⟨ σ   , x ≔ e₁ ⨾ e₂ ⟩   ≡> ⟨ σ' , int n₂ ⟩

