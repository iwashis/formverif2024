module lecture2 where

--
-- Wstępne importy:
--
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

--
-- Typ reprezentujący porządek na liczbach naturalnych:
--
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { n : ℕ } → zero ≤ n
  s≤s : ∀ { m } → ∀ { n } → m ≤ n → suc m ≤ suc n
--
-- Przykład dowodu
_ : 2 ≤ 5
_ = s≤s {1} {4} (s≤s {0} {3} ( z≤n {3}))

data _≥_≥_ : ℕ → ℕ → ℕ → Set where
 m≥n≥k : ∀ { m n k } → n ≤ m → k ≤ n → m ≥ n ≥ k
--
-- Ustalmy priorytety:
infix 4 _≤_

--
-- Możemy udowodnić następujące twierdzenie:
-- inv-s≤s : ∀ { m n } → suc m ≤ suc n → m ≤ n

inv-s≤s : ∀ { m n } → suc m ≤ suc n → m ≤ n
inv-s≤s {m} {n} (s≤s {m} {n} p) = p

--
-- Podobnie, możemy pokazać, iż:
-- inv-m≤zero : ∀ { m } → m ≤ zero → m ≡ zero



-- Twierdzenia oraz
-- dowody zwrotności i przechodniości
-- relacji ≤



--
-- Twierdzenie + dowód antysymetryczność
--


--
-- Nasz porządek jest liniowy (Total order)
-- Zwróćcie uwagę na notację!
--
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n
--
-- i porównajcie z taką definicją:
--
data Total' : ℕ → ℕ → Set where
  forward' : ∀ { m n } → m ≤ n → Total' m n
  flipped' : ∀ { m n } → n ≤ m → Total' m n
--
-- Jesteśmy teraz w stanie udowodnić
-- ≤-total : ∀ (m n : ℕ) → Total m n
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

--
-- Monotoniczność
--
-- Udowodnimy:
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
-- używając dwóch lematów:
-- +-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
-- oraz:
-- +-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
--

--
-- Nierówność ostra
data _<_ : ℕ → ℕ → Set where
-- ...

--
-- Ćwiczenia:
--
-- dowodnić przechodniość, monotoniczność dla <
-- oraz pokazać: < → ≤


-- Ćwiczenia:
--
-- Zdefiniujmy typy danych które przechowują informację o (nie)parzystości
-- danej liczby naturalnej
-- even i odd:
-- even : ℕ → Set
-- odd : ℕ → Set


-- Pokazujemy, że:
-- e+e≡e : ∀ { m n } → even m → even n → even ( m + n )
-- o+e≡e : ∀ { m n } → odd m → even n → odd ( m + n )
