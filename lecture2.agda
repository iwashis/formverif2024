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
inv-m≤zero : ∀ { m } → m ≤ zero → m ≡ zero
inv-m≤zero z≤n = refl


-- Twierdzenia oraz
-- dowody zwrotności i przechodniości
-- relacji ≤
≤-refl : ∀ { m } → m ≤ m
≤-refl {zero} = z≤n
≤-refl {suc m} = s≤s ≤-refl

≤-trans : ∀ { m n k } → m ≤ n → n ≤ k → m ≤ k
≤-trans {.zero} {n} {k} (z≤n {n}) _ = z≤n {k}
≤-trans {.(suc _)} {.(suc _)} {.(suc _)} (s≤s p1) (s≤s p2) = s≤s (≤-trans p1 p2)

--
-- Twierdzenie + dowód antysymetryczność
--
≤-antisym : ∀ { m n } → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
-- klasycznie drugą definicji można przedstawić następująco:
-- ≤-antisym {suc m} { suc n }(s≤s p1) (s≤s p2) = cong suc (≤-antisym p1 p2)
-- ale tym razem użyjmy słowa klucza rewrite:
≤-antisym {suc m} { suc n }(s≤s p1) (s≤s p2) rewrite ≤-antisym p1 p2 = refl

-- gdzie, typ cong (mniej więcej) wygląda następująco:
-- cong : (f: A->B) -> a ≡ b -> f a ≡ f b

-- Nasz porządek jest liniowy (Total order)
-- Zwróćcie uwagę na notację!
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
-- Monotoniczność (jest na slajdach, ale proszę nie ściągać i udowodnić
-- jako ćwiczenie)
-- Udowodnimy:
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
-- używając dwóch lematów:
-- +-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
-- oraz:
-- +-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
--

-- Ćwiczenia:
-- Nierówność ostra
data _<_ : ℕ → ℕ → Set where
-- ...
--
-- dowodnić przechodniość, monotoniczność dla <
-- oraz pokazać: < → ≤


-- Dalsza część wykładu:
-- Zdefiniujmy typy danych które przechowują informację o (nie)parzystości
-- danej liczby naturalnej
-- even i odd:
data even : ℕ → Set
data odd : ℕ → Set

data even where
  e_zero : even zero
  e_suc : ∀ { n } → odd n → even ( suc n )

data odd where
  o_suc : ∀ {n} → even n → odd (suc n)


-- Pokazujemy, że:
e+e≡e : ∀ { m n } → even m → even n → even ( m + n )
o+e≡o : ∀ { m n } → odd m → even n → odd ( m + n )

e+e≡e {zero} {n} _ p = p
e+e≡e {suc m} {n} (e_suc {m} proof_that_m_is_odd) p2 = e_suc helper
  where
    helper = o+e≡o proof_that_m_is_odd p2

o+e≡o {suc m} {n} (o_suc {m} even_m) even_n = o_suc helper
  where
    helper = e+e≡e even_m even_n
