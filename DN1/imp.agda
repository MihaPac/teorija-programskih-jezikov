module imp where


-- Logične vrednosti
data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

data Bool : Set where
    true : Bool
    false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

_and_ : Bool → Bool → Bool
true and true = true
true and false = false
false and _ = false

_or_ : Bool → Bool → Bool
true or _ = true
false or true = true
false or false = false

not_ : Bool → Bool
not true = false
not false = true

--for_:=_to_do_done : {A : Set} → A → 


{-
_AND_ : Bool → Bool → Bool
true AND true = true
true AND false = false
false AND _ = false

_OR_ : Bool → Bool → Bool
true OR _ = true
false OR true = true
false OR false = false

NOT_ : Bool → Bool
NOT true = false
NOT false = true
-}
-- Naravna števila

data Nat : Set where
    zero : Nat
    suc : Nat → Nat 

-- Namesto suc (suc zero) lahko napišemo kar 2
{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = suc (plus m n)

mnoz : Nat → Nat → Nat
mnoz zero n = zero
mnoz (suc m) n = plus n (mnoz m n)

potenca : Nat → Nat → Nat
potenca a zero = suc zero -- Napaka za 0 ** 0 ampak ta bi bila vedno
potenca a (suc b) = mnoz a (potenca a b)

equal : Nat → Nat → Bool
equal zero zero = true
equal zero (suc b) = false
equal (suc a) zero = false
equal (suc a) (suc b) = equal a b

less : Nat → Nat → Bool
less zero zero = false
less zero (suc b) = true
less (suc a) zero = false
less (suc a) (suc b) = less a b

more : Nat → Nat → Bool
more a b = not (less a b)
--more a b = NOT (less a b)

-- Seznami

data List : Set → Set where
    [] : {A : Set} → List A
    _::_ : {A : Set} → A → List A → List A

head : {A : Set} → List A → Maybe A 
head [] = nothing
head (x :: _) = just x

-- Končne množice

data Fin : Nat → Set where
    zero : {n : Nat} → Fin (suc n)
    suc : {n : Nat} → Fin n → Fin (suc n)

infixl 25 _/_

_/_ : (m n : Nat) → Fin (suc (plus m n))
zero / n = zero
suc m / n = suc (m / n)

-- Vektorji

data Vec : Set → Nat → Set where
    [] : {A : Set} → Vec A zero
    _::_ : {A : Set} {n : Nat} → A → Vec A n → Vec A (suc n)

_[_] : {A : Set} {n : Nat} → Vec A n → Fin n → A
[] [ () ]
(x :: v) [ zero ] = x
(x :: v) [ suc ind ] = v [ ind ]

_[_]←_ : {A : Set} {n : Nat} → Vec A n → Fin n → A → Vec A n
_[_]←_ [] ()
_[_]←_ (x :: xs) zero v = v :: xs
_[_]←_ (x :: xs) (suc i) v = x :: (xs [ i ]← v)


-- Sintaksa jezika

infixr 3 _；_ 
infix 4 _:=_
infix 5 IF_THEN_ELSE_END
infix 6 WHILE_DO_DONE
infix 6 SKIP

infix 10 _≡_
infix 10 _>_
infix 10 _<_

infixl 11 _+_
infixl 12 _*_

infix 14 !_
infix 15 `_

-- Artimetične in logične izraze ter ukaze parametriziramo z naravnim številom `n`,
-- ki pove, da izraz uporablja spremenljivke indeksirane med `0` in `n - 1`.

data Exp (n : Nat) : Set where
    `_ : Nat → Exp n
    !_ : Fin n → Exp n -- Spremenljivke nazivamo z naravnimi števili manjšimi od `n`
    _+_ : Exp n → Exp n → Exp n
    _*_ : Exp n → Exp n → Exp n
    _**_ : Exp n → Exp n → Exp n

data BExp (n : Nat) : Set where
    _≡_ : Exp n → Exp n → BExp n
    _<_ : Exp n → Exp n → BExp n
    _>_ : Exp n → Exp n → BExp n
    _AND_ : BExp n → BExp n → BExp n
    _OR_ : BExp n → BExp n → BExp n
    NOT_ : BExp n → BExp n

data Cmd : (n : Nat) → Set where
    IF_THEN_ELSE_END : {n : Nat} → BExp n → Cmd n → Cmd n → Cmd n
    WHILE_DO_DONE : {n : Nat} → BExp n → Cmd n → Cmd n
    _；_ : {n : Nat} → Cmd n → Cmd n → Cmd n
    _:=_ : {n : Nat} → (Fin n) → Exp n → Cmd n
    SKIP : {n : Nat} → Cmd n
    FOR_:=_TO_DO_DONE : {n : Nat} → (Fin n) → Exp n → Exp n → Cmd n → Cmd n
    -- Bi naj tu bila Fin n za tisto spremenljivko ali kaj drugega?
    -- Dodal "bencin" v obliki Nat
    PRINT : {n : Nat} → Exp n → Cmd n
    -- sešteje vrednosti spremenljivk na mestu 1 in 0 v stanju s tremi spremenljivkami. 
primer : Exp 3
primer = ! 1 / 1 + ! 0 / 2 -- Da lahko uporabimo vrednost na mestu 0 in 1 v izrazu velikosti do 3.

-- Program, ki sešteje prvih n naravnih števil
--vsota : Nat → Cmd 3
--vsota n = 
--    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
--    1 / 1 := ` 0 ；
--    2 / 0 :=  ! (0 / 2) ；
--    WHILE ! (1 / 1) < ! (0 / 2) DO
--        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
--        1 / 1 := ! 1 / 1 + ` 1
--    DONE

-- Program, ki sešteje prvih n naravnih števil s pomočjo for zanke
vsota : Nat → Cmd 3
vsota n = 
     0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
     1 / 1 := ` 0 ；
     2 / 0 := ` 0 ；
     FOR ( (1 / 1) ) := ` 0 TO ! (0 / 2) DO
         2 / 0 := ! 2 / 0 + ! 1 / 1 ；
         1 / 1 := ! 1 / 1 + ` 1 ； PRINT (! (2 / 0))
     DONE


-- Stanje

State : Nat → Set
State n = Vec Nat n

--Result : Nat → Set
--Result n = State n

-- Če želite, lahko za nadgradnjo rezultatov uporabite spodnje tipe

record Pair (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B

-- Result : Nat → Set
-- Result n = Pair (State n) (List Nat)



Result : Nat → Set
Result n = Pair (Maybe (State n)) (List Nat)

evalExp : {n : Nat} → State n → Exp n → Nat
evalExp st (` x) = x
evalExp st (! i) = st [ i ]
evalExp st (exp₁ + exp₂) = plus (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ * exp₂) = mnoz (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ ** exp₂) = potenca (evalExp st exp₁) (evalExp st exp₂)

evalBExp : {n : Nat} → State n → BExp n → Bool
evalBExp st (x ≡ y) = equal (evalExp st x) (evalExp st y)
evalBExp st (x < y) = less (evalExp st x) (evalExp st y)
evalBExp st (x > y) = more (evalExp st x) (evalExp st y)
evalBExp st (b AND d) = (evalBExp st b) and (evalBExp st d)
evalBExp st (b OR d) = (evalBExp st b) or (evalBExp st d)
evalBExp st (NOT b) = not (evalBExp st b)

evalCmd : {n : Nat} → Nat → Result n → Cmd n → Result n
evalCmd _ (nothing , nats) cmd = nothing , nats -- ce je zmanjkalo goriva kadarkoli prej, ne bo nic vec delal in bo koncal tam
evalCmd n (just st , nats) IF bexp THEN cmd₁ ELSE cmd₂ END =
          if evalBExp st bexp
            then evalCmd n (just st , nats) cmd₁
          else evalCmd n (just st , nats) cmd₂
-- evalCmd zero (st , nats) WHILE bexp DO cmd DONE = nothing , nats -- Zmanjka goriva in je konec za vedno
evalCmd (suc n) (just st , nats) WHILE bexp DO cmd DONE =
          if evalBExp st bexp
            then evalCmd n (just st , nats) (cmd ； (WHILE bexp DO cmd DONE))
          else (just st , nats)
evalCmd n (st , nats) (cmd ； cmd₁) = evalCmd n (evalCmd n (st , nats) cmd) cmd₁
evalCmd _ (just st , nats) (ℓ := exp) = just (st [ ℓ ]← (evalExp st exp)) , nats
evalCmd (suc n) (st , nats) SKIP = st , nats
evalCmd zero (_ , nats) _ = nothing , nats
evalCmd (suc n) (just st , nats) FOR x := a TO b DO cmd DONE =
             if (evalBExp st (b < a))
               then (just st , nats)
             else
               (evalCmd n (just st , nats) (cmd ； FOR x := (a + ` 1) TO b DO cmd DONE))
evalCmd (suc n) (just st , nats) (PRINT (` exp)) = just st , (exp :: nats)
evalCmd (suc n) (just st , nats) (PRINT (! exp)) = just st , ((st [ exp ]) :: nats)
evalCmd (suc n) (just st , nats) (PRINT (exp₁ + exp₂)) = just st , (plus (evalExp st exp₁) (evalExp st exp₂) :: nats)
evalCmd (suc n) (just st , nats) (PRINT (exp₁ * exp₂)) = just st , (mnoz (evalExp st exp₁) (evalExp st exp₂) :: nats)
evalCmd (suc n) (just st , nats) (PRINT (exp₁ ** exp₂)) = just st , (potenca (evalExp st exp₁) (evalExp st exp₂) :: nats)
{- Napaka v misljenju: PRINT samo potreben pred izrazi, ne pa pred ukazi
evalCmd (suc n) (just st , nats) (PRINT IF bexp THEN cmd ELSE cmd₁ END) = 
          if evalBExp st bexp
            then evalCmd (suc n) (just st , nats) (PRINT cmd)
          else evalCmd (suc n) (just st , nats) (PRINT cmd₁)
evalCmd (suc n) (just st , nats) (PRINT WHILE bexp DO cmd DONE) = 
          if evalBExp st bexp
            then evalCmd n (just st , nats) (PRINT (cmd ； WHILE bexp DO cmd DONE))
          else (just st , nats)
evalCmd (suc n) (just st , nats) (PRINT (cmd ； cmd₁)) = evalCmd n (just st , nats) ((PRINT cmd) ； (PRINT cmd₁))
evalCmd (suc n) (just st , nats) (PRINT (x := x₁)) = evalCmd (suc n) (just st , ((evalExp st x₁) :: nats)) (x := x₁)
evalCmd (suc n) (just st , nats) (PRINT SKIP) = evalCmd (suc n) (just st , nats) SKIP
evalCmd (suc n) (just st , nats) (PRINT FOR x := a TO b DO cmd DONE) = 
          if evalBExp st (a < b)
            then evalCmd n (just st , nats) (PRINT (cmd ； FOR x := (a + ` 1) TO b DO cmd DONE)) 
          else (just st , nats)
evalCmd (suc n) (just st , nats) (PRINT (PRINT cmd)) = evalCmd (suc n) (just st , nats) (PRINT cmd)
-}
-- Pozor: tip funkcije ima smisel zgolj za osnovni tip rezultata
--vsotaPrvihN : Nat → Nat
--vsotaPrvihN n = (evalCmd 125 ( 0 :: (0 :: (0 :: []))) (vsota n)) [ 0 / 2 ]

b = evalCmd 255 (just ( 0 :: (0 :: (0 :: []))) , []) (vsota 45)
c = head (Pair.snd b)
d = Pair.fst b

Σn : Nat → Maybe Nat
Σn n = head (Pair.snd (evalCmd 255 (just ( 0 :: (0 :: (0 :: []))) , []) (vsota n)))
