module lecture2 where

--
-- wstępne importy:
--
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

--
-- Typ reprezentujący porządek na liczbach naturalnych:
--
data _≤_ : ℕ → ℕ → Set where

--
-- Przykład dowodu



--
-- Ustalmy priorytety:
infix 4 _≤_

--
-- Możemy udowodnić następujące twierdzenie:
-- inv-s≤s : ∀ { m n } → suc m ≤ suc n → m ≤ n



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
-- Nasz porządek jest całkowity (Total order)
-- Zwróćcie uwagę na notację!
--
data Total (m n : ℕ) : Set where


--
-- i porównajcie z taką definicją:
--
data Total′ : ℕ → ℕ → Set where

--
-- Jesteśmy teraz w stanie udowodnić
-- ≤-total : ∀ (m n : ℕ) → Total m n
--



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


-- Ćwiczenia:
-- dowodnić przechodniość, monotoniczność dla <
-- oraz pokazać: < → ≤



-- Zdefiniujmy typy danych które przechowują informację o (nie)parzystości
-- danej liczby naturalnej
-- even i odd:
-- even : ℕ → Set
-- odd : ℕ → Set


-- Pokazujemy, że:
-- e+e≡e : ∀ { m n } → even m → even n → even ( m + n )
-- o+e≡e : ∀ { m n } → odd m → even n → odd ( m + n )
