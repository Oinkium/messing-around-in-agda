module Game-Morphs where
-- in which we describe many copycat-shaped strategies

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)

open import Game-Core

dist01 : ∀ {M} → (I ⊘ M) ≈ I
dist01 {gam f} = bsm (sim ⊥-elim λ())
                     (sim ⊥-elim λ())

dist02 : ∀ {P} → (P ⊸ I) ≈ I
dist02 {gam f} = bsm (sim ⊥-elim λ())
                     (sim ⊥-elim λ())

mutual
  unit⊸ : ∀ {M} → (I ⊸ M) ≈ M
  unit⊸ {gam f} = bsm (sim id (λ m → wk₁ $ unit⊗ {f m}))
                      (sim id (λ m → wk₂ $ unit⊗ {f m}))

  unit⊗ : ∀ {M} → (M ⊗ I) ≈ M
  unit⊗ {gam f}
       = bsm (sim ([ id , ⊥-elim ])
                  ([ (λ m → wk₁ $ unit⊸ {f m}) , (λ()) ] ))
             (sim inj₁ (λ m → wk₂ $ unit⊸ {f m}))

unit⊘ : ∀ {M} → M ⊘ I ≈ M
unit⊘ {gam f} = bsm (sim id (λ i → wk₁ $ unit⊸))
                    (sim id (λ i → wk₂ $ unit⊸))

sym⊗ : ∀ {M N} → (M ⊗ N) ≈ (N ⊗ M)
sym⊗ {gam f} {gam g}
   = bsm (sim [ inj₂ , inj₁ ]
              [ (λ _ → id≲) , (λ _ → id≲) ])
         (sim [ inj₂ , inj₁ ]
              [ (λ _ → id≲) , (λ _ → id≲) ])

dist10 : ∀ {M} → (I ⊗ M) ≈ M
dist10 = sym⊗ ≈∘≈ unit⊗

dec1 : ∀ {M N} → M ⊗ N ≈ (M ⊘ N) ×' (N ⊘ M)
dec1 {gam f} {gam g}
   = bsm (sim id (λ _ → id≲))
         (sim id (λ _ → id≲))
                          
dist1 : ∀ {M N O} → (M ×' N) ⊘ O ≈ (M ⊘ O) ×' (N ⊘ O)
dist1 {gam f} {gam g} {gam h}
    = bsm (sim id [ (λ _ → id≲) , (λ _ → id≲) ])
          (sim id [ (λ _ → id≲) , (λ _ → id≲) ])

dist1ω : ∀ {M N} → (ω× M) ⊘ N ≈ ω× (M ⊘ N)
dist1ω {gam f} {gam g} = bsm (sim id (λ _ → id≲)) (sim id (λ _ → id≲))

dist2 : ∀ {M N O} → O ⊸ (M ×' N) ≈ (O ⊸ M) ×' (O ⊸ N)
dist2 {gam f} {gam g} {gam h}
    = bsm (sim id [ (λ _ → id≲) , (λ _ → id≲) ])
          (sim id [ (λ _ → id≲) , (λ _ → id≲) ])

dist2ω : ∀ {M N} → M ⊸ (ω× N) ≈ ω× (M ⊸ N)
dist2ω {gam f} {gam g} = bsm (sim id (λ _ → id≲)) (sim id (λ _ → id≲))

sym× : ∀ {M N} → M ×' N ≈ N ×' M
sym× {gam f} {gam g}
   = bsm (sim [ inj₂ , inj₁ ] [ (λ _ → id≲) , (λ _ → id≲) ])
         (sim [ inj₂ , inj₁ ] [ (λ _ → id≲) , (λ _ → id≲) ])   

lfe : ∀ {M N} → (M ⊸ N) ⊸o ≈ (N ⊸o) ⊘ M
lfe {gam f} {gam g}
  = bsm (sim id (λ _ → id≲))
        (sim id (λ _ → id≲))

curryo : ∀ {M N} → M ⊸ (N ⊸o) ≈ (N ⊗ M) ⊸o
curryo {gam f} {gam g}
  = bsm (sim id (λ _ → id≲))
        (sim id (λ _ → id≲))

↑≈⊸o : ∀ {M} → M ⊸o ≈ M ⊸ o
↑≈⊸o = bsm (sim (λ _ → tt) (λ _ → wk₂ $ sym⊗ ≈∘≈ unit⊗))
           (sim (λ _ → tt) (λ _ → wk₁ $ sym⊗ ≈∘≈ unit⊗))

-- We can apply isomorphisms underneath actions:

mutual

  _⊸≲_ : ∀ {M N} O → N ≲ M → (O ⊸ N) ≲ (O ⊸ M)
  _⊸≲_ {gam f} {gam g} (gam h) (sim f' g')
       = sim f' (λ m → g' m ≲⊗ (gam h))

  _≲⊗_ : ∀ {M N} → M ≲ N → ∀ O → (M ⊗ O) ≲ (N ⊗ O)
  _≲⊗_ {gam f} {gam g} (sim f' g') (gam h) 
       = sim [ inj₁ ∘ f' , inj₂ ]
              [ (λ m → gam h ⊸≲ (g' m)) ,
                (λ o' → (sim f' g') ≲⊸ (h o')) ]

  _≲⊸_ : ∀ {M N} → N ≲ M → ∀ O → (M ⊸ O) ≲ (N ⊸ O)
  _≲⊸_ {gam f} {gam g} s (gam h) =
        sim id (λ o' → h o' ⊗≲ s)

  _⊗≲_ : ∀ {M N} O → M ≲ N → (O ⊗ M) ≲ (O ⊗ N)
  _⊗≲_ {M} {N} O s = (wk₁ $ sym⊗) ≲∘≲ (s ≲⊗ O) ≲∘≲ (wk₁ $ sym⊗)

_≲⊘_ : ∀ {M N} → M ≲ N → ∀ O → (M ⊘ O) ≲ (N ⊘ O)
_≲⊘_ {gam f} {gam g} (sim f' g') (gam h)
     = sim f' (λ m → gam h ⊸≲ (g' m))

_⊘≲_ : ∀ {M N} O → M ≲ N → (O ⊘ M) ≲ (O ⊘ N)
(gam o) ⊘≲ s = sim id (λ m → s ≲⊸ (o m))

_⊗≈_ : ∀ {M N} O → M ≈ N → (O ⊗ M) ≈ (O ⊗ N)
O ⊗≈ s = bsm (O ⊗≲ wk₂ s) (O ⊗≲ wk₁ s)

_≈⊘_ : ∀ {M N} → M ≈ N → ∀ O → (M ⊘ O) ≈ (N ⊘ O)
s ≈⊘ O = bsm (wk₂ s ≲⊘ O) (wk₁ s ≲⊘ O)

_⊘≈_ : ∀ {M N} O → M ≈ N → O ⊘ M ≈ O ⊘ N
O ⊘≈ s = bsm (O ⊘≲ (wk₂ s)) (O ⊘≲ (wk₁ s))

_⊸≈_ : ∀ {M N} O → M ≈ N → (O ⊸ M) ≈ (O ⊸ N)
O ⊸≈ s = bsm (O ⊸≲ (wk₂ s)) (O ⊸≲ (wk₁ s))

_≈⊸_ : ∀ {M N} → M ≈ N → ∀ O → (M ⊸ O) ≈ (N ⊸ O)
s ≈⊸ O = bsm (wk₁ s ≲⊸ O) (wk₂ s ≲⊸ O)

lfe' : ∀ {M N} → (M ⊸ N) ⊸ o ≈ (N ⊸ o) ⊘ M
lfe' {M} {N} = (↑≈⊸o ^-1) ≈∘≈ lfe ≈∘≈ (↑≈⊸o ≈⊘ M)

-- ↑≈⊸o ≈⊘ M ≈∘≈ (lfe ≈∘≈ ↑≈⊸o ^-1)

mutual
  pasc⊸ : ∀ {M N O} → M ⊸ (N ⊸ O) ≈ (M ⊗ N) ⊸ O
  pasc⊸ {gam m} {gam n} {gam o}
      = bsm (sim id (λ i → (o i ⊗≲ (wk₂ $ sym⊗)) ≲∘≲
                           (wk₁ $ asc⊗ {o i} {gam n} {gam m})))
            (sim id (λ i → (wk₂ $ asc⊗ {o i} {gam n} {gam m}) ≲∘≲
                           (o i ⊗≲ (wk₁ $ sym⊗))))

  asc⊗ : ∀ {M N O} → (M ⊗ N) ⊗ O ≈ M ⊗ (N ⊗ O)
  asc⊗ {gam m} {gam n} {gam o}
     = bsm (sim [ [ inj₁ , inj₂ ∘ inj₁ ] , inj₂ ∘ inj₂ ]
                [ [ (λ i → (wk₂ (sym⊗) ≲⊸ (m i)) ≲∘≲
                           (wk₁ $ pasc⊸ {gam o} {gam n} {m i}))
                  , (λ i → wk₂ $ psym⊸ {gam m} {gam o} {n i}) ]
                  , (λ i → wk₂ $ pasc⊸ {gam m} {gam n} {o i}) ])
           (sim [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ] ]
                [ (λ i → _≲∘≲_ (wk₂ $ pasc⊸ {gam o} {gam n} {m i})
                              (wk₁ (sym⊗) ≲⊸ (m i)))
                , [ (λ i → wk₂ $ psym⊸ {gam o} {gam m} {n i})
                  , (λ i → wk₁ $ pasc⊸ {gam m} {gam n} {o i}) ] ])

  psym⊸ : ∀ {M N O} → M ⊸ (N ⊸ O) ≈ N ⊸ (M ⊸ O)
  psym⊸ = pasc⊸ ≈∘≈ (sym⊗ ≈⊸ _) ≈∘≈ (pasc⊸ ^-1)

pasc⊘ : ∀ {M N O} → (M ⊘ N) ⊘ O ≈ M ⊘ (N ⊗ O)
pasc⊘ {gam m} {gam n} {gam o}
    = bsm (sim id (λ i → (wk₂ (sym⊗) ≲⊸ (m i)) ≲∘≲ (wk₁ $ pasc⊸)))
          (sim id (λ i → (wk₂ $ pasc⊸) ≲∘≲ (wk₂ (sym⊗) ≲⊸ (m i))))

psym⊘ : ∀ {M N O} → (M ⊘ N) ⊘ O ≈ (M ⊘ O) ⊘ N
psym⊘ = pasc⊘ ≈∘≈ (_ ⊘≈ sym⊗) ≈∘≈ (pasc⊘ ^-1)

mutual
  ≲⊗af : ∀ {M N} → M ⊗ N ≲ M
  ≲⊗af {gam g} {gam _} = sim inj₁ (λ m → ≲⊸af {g m})

  ≲⊸af : ∀ {M N} → M ≲ N ⊸ M
  ≲⊸af {gam g} = sim id (λ m → ≲⊗af {g m})

≲⊘af : ∀ {M N} → M ⊘ N ≲ M
≲⊘af {gam _} = sim id (λ m → ≲⊸af)

≲wk : ∀ {M N} → M ⊗ N ≲ M ⊘ N
≲wk {gam _} {gam _} = sim inj₁ (λ x → id≲)

≲I : ∀ {M} → M ≲ I
≲I = sim ⊥-elim (λ())

abs : ∀ {M} → o ⊘ M ≈ o
abs {M} = (unit⊸ ^-1) ≈⊘ M ≈∘≈ (lfe' {M} {I} ^-1) ≈∘≈ dist02 {M} ≈⊸ o ≈∘≈ unit⊸

≲π₁ : ∀ {M N} → M ×' N ≲ M
≲π₁ {gam _} {gam _} = sim inj₁ (λ _ → id≲)

≲π₂ : ∀ {M N} → M ×' N ≲ N
≲π₂ {gam _} {gam _} = sim inj₂ (λ _ → id≲)

≲π : ∀ {M} → ℕ → ω× M ≲ M
≲π {gam _} n = sim (λ m → n , m) (λ _ → id≲)

⊸≲⊸̂ : ∀ {M N} → M ⊸̂ N ≲ M ⊸ N
⊸≲⊸̂ {gam m} {gam n} = sim id (λ n' → ≲wk {gam m} {n n'} ≲∘≲ (wk₂ sym⊗))
