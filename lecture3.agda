module lecture3 where

data _≡_  { A : Set } ( x : A ) : A → Set where
  refl : x ≡ x

-- przykład równoważnego definiowania równości
data _≡'_  : ∀ { A : Set } → A → A → Set₁ where
  refl : ∀ { A : Set } → ∀ { x : A } → x ≡' x


infix 4 _≡_

sym : ∀ { A : Set } → { x y : A } → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ { A  : Set } → { x y z : A } → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl


cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl Px = Px


module ≡-Reasoning {A : Set} where

   infix  1 begin_
   infixr 2 _≡⟨⟩_ step-≡
   infix  3 _∎

   begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
   begin eq = eq

   _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
   x ≡⟨⟩ eq = eq

   step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
   step-≡ x refl x≡y = x≡y

   syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

   _∎ : ∀ (x : A) → x ≡ x
   x ∎ = refl

open ≡-Reasoning

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

sym-≐ : ∀ { A : Set } → ∀ { x y : A } → x ≐ y → y ≐ x -- ∀ ( P ) → P y → P x
sym-≐ {A} {x} {y} x≐y P Py = x≐y Q (λ x → x) Py
  where
   Q : A → Set
   Q z = P z → P x
