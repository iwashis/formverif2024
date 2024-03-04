%title: Metody Formalne, wykład 1 
%author: Tomasz Brengos
%date: 2024-02-26


-> # Instalacja Agda i IDE <- 
==============

* Emacs (doom)
* Agda mode
* Agda std-lib (1.7.3)


--------------------------------------------------
-> # Pierwszy moduł <-

```agda 

module lecture1 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

```
--------------------------------------------------
-> # Typ reprezentujący liczby naturalne <-
==============

Definicja typu reprezentującego liczby naturalne:


```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
```

Definicja dodawania

```agda
_+_ : ℕ → ℕ → ℕ
...
```

--------------------------------------------------

-> # Pierwsze twierdzenie <-
==============
```
_ : 2 + 2 ≡ 4
```

-------------------------------------------------

-> # Automatyzacja twierdzeń <-
==============
```
_ : 5 + 2 ≡ 7
```

-------------------------------------------------

-> # Typy zależne i dowody <-
=============

Rozważmy następującą deklarację typu funkcji:


```
+_zero-neutral : ∀ (m : ℕ ) → m + zero ≡ m
```

-------------------------------------------------

-> # Dalsze kroki <-
=============

```agda 
_*_ : ℕ → ℕ → ℕ
*-right-zero : ∀ ( m : ℕ ) → m * zero ≡ zero
+-assoc : ∀ (m n p : ℕ) → ( m + n ) + p ≡ m + ( n + p )
+-identity_r : ∀ (m : ℕ) → m + zero ≡ m
+-suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-commutativity : ∀ ( m n : ℕ ) → m + n ≡ n + m
```

Mozemy uzywać słowa klucza `rewrite`:


```agda 
+-assoc2 : ∀ ( m n p : ℕ ) → (m + n) + p ≡ m + (n + p)
+-assoc2 zero n p = refl
+-assoc2 (suc m) n p rewrite +-assoc m n p = refl
```


-------------------------------------------------

-> # Ćwiczenie 1 <- 
============

* Zdefiniować typ reprezentujący listę
* Zdefiniować operację konkatenacji dwóch list 
* Udowodnić własności konkatenacji (np. równości monoidowe)



-------------------------------------------------

-> # Ćwiczenie 2 <-
============
Rozważmy następującą definicję postaci binarnej liczb 
naturalnych:

```agda 
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
```

Zdefiniować `inc: Bin → Bin` oraz dla przedstawionych
```agda 
to   : ℕ → Bin
from : Bin → ℕ
```
udowodnić zgodność obu definicji.


