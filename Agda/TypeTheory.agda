module TypeTheory where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Primitive

data Product {n : Level} (A : Set n) (B : Set n) : (Set (lsuc n)) where
  Pr : A → B → Product A B

p1 : Product Nat Nat
p1 = Pr 2 3

indProduct : (A B : Set) (P : Product A B → Set) →
            (∀ (a : A) (b : B) → P (Pr a b)) →
            (p : Product A B) → P p
indProduct _ _ _ g (Pr a' b') = g a' b'

recProduct : (A B P : Set) (g : A → B → P) → Product A B → P
recProduct A B P g = indProduct A B (\ _ → P) g

pr₁ : {A B : Set} → Product A B → A
pr₁ (Pr a _) = a

pr₂ : {A B : Set} → Product A B → B
pr₂ (Pr _ b) = b

uniqProd : (A B : Set) (p : Product A B) → (Pr (pr₁ p) (pr₂ p)) ≡ p
uniqProd A B (Pr x x₁) = refl

data Sigma {n : Level} (A : Set (lsuc n)) (B : A → Set n) : Set (lsuc n) where
  Sig : (a : A) → B a → Sigma A B

indSigma : {n : Level} {A : Set (lsuc n)} {B : A → Set n} (P : Sigma A B → Set (lsuc n))
         (g : (a : A) (b : B a) → P (Sig a b)) →
         (p : Sigma A B) → P p
indSigma P g (Sig a b) = g a b

recSigma : {n : Level} {A : Set (lsuc n)} {B : A → Set n} (P : Set (lsuc n)) →
          ((a : A) → B a → P) → (p : Sigma A B) → P
recSigma P g = indSigma (λ _ → P) g

sig₁ : {n : Level} {A : Set (lsuc n)} {B : A → Set n} → Sigma A B → A
sig₁ {n} {A} = recSigma A (λ a b → a)

sig₂ : {n : Level} {A : Set (lsuc n)} {B : A → Set n} → (p : Sigma A B) → B (sig₁ p)
sig₂ {n} {A} {B} (Sig a x) = x
-- indSigma (λ p → B (sig₁ p)) (λ a b → b)

Magma : {n : Level} → (Set (lsuc n))
Magma {n} = Sigma (Set n) (λ A → A → A → A)

data Coproduct {A B : Set} : Set where
  Inl : A → Coproduct
  Inr : B → Coproduct

c : Coproduct
c = Inl 3

rectCoproduct : ∀ {A B} → (C : Set) → (A → C) → (B → C) →
                 Coproduct {A} {B} → C
rectCoproduct C g1 g2 (Inl x) = g1 x
rectCoproduct C g1 g2 (Inr x) = g2 x

indCoproduct : ∀ {A B} → (C : Coproduct {A} {B} → Set) →
                 (∀ (a : A) → C (Inl a)) →
                 (∀ (b : B) → C (Inr b)) →
                 ∀ c → C c
indCoproduct C g1 g2 (Inl x) = g1 x
indCoproduct C g1 g2 (Inr x) = g2 x
