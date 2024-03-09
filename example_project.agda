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

-- typ dzięki ktoremu jestesmy w stanie wywnioskować czy dane przypisanie jest w kontekście
data _⊢_≔_ : Cntxt → Var → ℕ → Set where
  top : ∀ { x } → ∀ {n} → ∀ { σ } → (x ⇉ n , σ) ⊢ x ≔ n
  tail : ∀ { x y } → ∀ { m n } → ∀ { σ  } → ( σ  ⊢ x ≔ n ) → ( y ⇉ m , σ ) ⊢ x ≔ n

-- typ, dzięki ktoremu będziemy mieli pewność, że nie dorzucimy dwa razy tej samej
-- nazwy zmiennej do kontekstu
data _∉_ : Var → Cntxt → Set where
  x∉Ø : ∀ { x } → x ∉ Ø
  x∉σ : ∀ { x y } →  ∀ {σ } → ∀ { n } → ¬ (x ≡ y) → x ∉ σ → x ∉ ( y ⇉ n , σ )

-- dorzucienie nowej komórki do pamięci
_⟦_≔_⟧ : Cntxt → Var → ℕ → Cntxt
σ ⟦ x ≔ n ⟧ = x ⇉ n , σ

-- Pary: pamięć, wyrażenie
Config : Set
Config = Cntxt × Exp



-- Small-step semantics--
data _↘_ : Config → Config → Set where
  varred : ∀ { x : Var } → ∀ { n } → ∀ { σ : Cntxt }
            → σ ⊢ x ≔ n
            ------------------------------------------------------
            → ⟨ σ  , var x  ⟩ ↘  ⟨ σ  , int n ⟩

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
  refl : ∀ { c } → (c ↣ c)
  _andThen_ : ∀ {c c' c'' } → (c ↘ c') → (c' ↣ c'') → (c ↣ c'')

infixr 6 _andThen_

pure : ∀ { c c' } → c ↘ c' → c ↣ c'
pure x = x andThen refl

-- Przypomnijmy sobie nasze wyrażenie:
-- example₁ = foo ≔ ( int 6 ) ⨾ (((int 7) ⊗ (int 8)) ⊕ (var foo))
first_step : ⟨ Ø , example₁ ⟩ ↘ ⟨ ( foo ⇉ 6 , Ø ) , ((int 7) ⊗ (int 8)) ⊕ (var foo) ⟩
first_step = asgint x∉Ø


_ : ⟨ Ø , example₁ ⟩ ↣ ⟨ ( foo ⇉ 6 , Ø )  , int 62 ⟩
_ = first_step andThen
    (rightadd (varred top)) andThen
    (leftadd mul) andThen
    add andThen refl


-- Big-step semantics

data _≡>_ : Config → Config → Set where
  intrefl : ∀ { σ } → ∀ { n }
            ------------------------------------------------------
          → ⟨ σ , int n ⟩ ≡> ⟨ σ , int n ⟩

  varred : ∀ { x : Var } → ∀ { n } → ∀ { σ : Cntxt }
          → σ ⊢ x ≔ n
            ------------------------------------------------------
          → ⟨ σ  , var x  ⟩  ≡> ⟨ σ  , int n ⟩

  add : ∀ { σ σ' σ'' } → ∀ { n₁ n₂ } → ∀ { e₁ e₂ }
          → ⟨ σ   , e₁ ⟩      ≡> ⟨  σ'' , int n₁ ⟩
          → ⟨ σ'' , e₂ ⟩      ≡> ⟨  σ' , int n₂ ⟩
            ------------------------------------------------------
          → ⟨ σ   , e₁ ⊕ e₂ ⟩ ≡> ⟨  σ' , int( n₁ + n₂ ) ⟩

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

------------------------------------
--
-- Zgodność semantyk
--
------------------------------------



-- Lematy potrzebne do udowodnienia zgodności
lemma₁ : ∀ { σ σ' } → ∀ { n n' }
       → ⟨ σ , int n ⟩ ↣ ⟨ σ' , int n' ⟩
       → n ≡ n'
lemma₁ refl = refl

lemma₂ : ∀ { σ σ' } → ∀ { n n' }
       → ⟨ σ , int n ⟩ ↣ ⟨ σ' , int n' ⟩
       → σ ≡ σ'
lemma₂ refl = refl

lemma₃ : ∀ { σ σ' } → ∀ { m₁ m₂ n }
       → ⟨ σ , int (m₁ + m₂) ⟩ ↣ ⟨ σ' , int n ⟩
       → m₁ + m₂ ≡ n
lemma₃ refl = refl

lemma₄ : ∀ { σ σ' } → ∀ { m₁ m₂ n }
         → ⟨ σ , int (m₁ * m₂) ⟩ ↣ ⟨ σ' , int n ⟩
       → m₁ * m₂ ≡ n
lemma₄ refl = refl


-- Zgodność semantyki small-step z big-step:
-- jeśli small-step semantics pozwala na obliczenie z e do int n (przy odpowiednich kontekstach)
-- to big-step semantics też na to pozwala:
theorem₁ : ∀ { σ σ' } → ∀ { e } → ∀ { n }
          → ⟨ σ , e ⟩ ↣ ⟨ σ' , int n ⟩
          → ⟨ σ , e ⟩ ≡> ⟨ σ' , int n ⟩
theorem₁ refl = intrefl
theorem₁ {σ} {σ'} {e} {n} (varred {x} {n₁} σ⊢x≔n₁ andThen step) rewrite lemma₁ step | lemma₂ step = varred σ⊢x≔n₁
theorem₁ (leftadd smol andThen step) = {!!}
theorem₁ (rightadd smol andThen step) = {!!}
theorem₁ {σ} {σ'} {e} {n} ((add {σ} {m₁} {m₂}) andThen step) with lemma₁ step | lemma₂ step | lemma₃ {σ} {σ'} {m₁} {m₂} {n} step
... | refl | refl | refl = add intrefl intrefl
theorem₁ (leftmul x andThen x₁) = {!!}
theorem₁ (rightmul x andThen x₁) = {!!}
theorem₁ {σ} {σ'} {e} {n} ((mul {σ} {m₁} {m₂}) andThen step) with lemma₁ step | lemma₂ step | lemma₄ {σ} {σ'} {m₁} {m₂} {n} step
... | refl | refl | refl = mul intrefl intrefl
theorem₁ {σ} {σ'} {e} {n} (asg smol andThen step) = {!!}
theorem₁ (asgint x andThen step) = asg intrefl x (theorem₁ step)
