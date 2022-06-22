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

_and_ : Maybe Bool → Maybe Bool → Maybe Bool
nothing and _ = nothing
_ and nothing = nothing
just true and just true = just true
just true and just false = just false
just false and just true = just false
just false and just false = just false

_or_ : Maybe Bool → Maybe Bool → Maybe Bool
nothing or _ = nothing
_ or nothing = nothing
just true or just _ = just true
just false or just y = just y

not_ : Maybe Bool → Maybe Bool
not nothing = nothing
not just true = just false
not just false = just true

-- Naravna števila

data Nat : Set where
    zero : Nat
    suc : Nat → Nat 

-- Namesto suc (suc zero) lahko napišemo kar 2
{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Maybe Nat
plus zero y = just y
plus (suc x) y = {!suc (plus x y)!}

mnoz : Maybe Nat → Maybe Nat → Maybe Nat

potenca : Maybe Nat → Maybe Nat → Maybe Nat

equal : Maybe Nat → Maybe Nat → Maybe Bool

less : Maybe Nat → Maybe Nat → Maybe Bool

more : Maybe Nat → Maybe Nat → Maybe Bool

{-
-- Seznami

data List : Set → Set where
    [] : {A : Set} → List A
    _::_ : {A : Set} → A → List A → List A


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
-- Primer aritmetičnega izraza, ki sešteje vrednosti spremenljivk na mestu 1 in 0 v stanju s tremi spremenljivkami. 
primer : Exp 3
primer = ! 1 / 1 + ! 0 / 2 -- Da lahko uporabimo vrednost na mestu 0 in 1 v izrazu velikosti do 3.

-- Program, ki sešteje prvih n naravnih števil
vsota : Nat → Cmd 3
vsota n = 
    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    1 / 1 := ` 0 ；
    2 / 0 :=  ! (0 / 2) ；
    WHILE ! (1 / 1) < ! (0 / 2) DO
        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
        1 / 1 := ! 1 / 1 + ` 1
    DONE

-- Program, ki sešteje prvih n naravnih števil s pomočjo for zanke
-- vsota : Nat → Cmd 3
-- vsota n = 
--     0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
--     1 / 1 := ` 0 ；
--     2 / 0 := ` 0 ；
--     FOR ( (1 / 1) ) := ` 1 TO ! (0 / 2) DO
--         2 / 0 := ! 2 / 0 + ! 1 / 1 ；
--         1 / 1 := ! 1 / 1 + ` 1 ； PRINT (! (2 / 0))
--     DONE


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

evalExp : {n : Nat} → Maybe (State n) → Exp n → Nat
evalExp st (` x) = x
evalExp nothing (! i) = 0
evalExp (just st) (! i) = st [ i ]
evalExp st (exp₁ + exp₂) = plus (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ * exp₂) = mnoz (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ ** exp₂) = potenca (evalExp st exp₁) (evalExp st exp₂)

evalBExp : {n : Nat} → Maybe (State n) → BExp n → Bool
evalBExp st (x ≡ y) = equal (evalExp st x) (evalExp st y)
evalBExp st (x < y) = less (evalExp st x) (evalExp st y)
evalBExp st (x > y) = more (evalExp st x) (evalExp st y)
evalBExp st (b AND d) = (evalBExp st b) and (evalBExp st d)
evalBExp st (b OR d) = (evalBExp st b) or (evalBExp st d)
evalBExp st (NOT b) = not (evalBExp st b)

evalCmd : {n : Nat} → Nat → Result n → Cmd n → Result n
evalCmd n (st , nats) IF bexp THEN cmd ELSE cmd₁ END =
          if evalBExp st bexp
            then evalCmd n (st , nats) cmd
          else evalCmd n (st , nats) cmd₁
evalCmd zero (st , nats) WHILE bexp DO cmd DONE = st , nats
evalCmd (suc n) (st , nats) WHILE bexp DO cmd DONE =
          if evalBExp st bexp
            then evalCmd n (st , nats) cmd
          else (st , nats)
evalCmd n (st , nats) (cmd ； cmd₁) = evalCmd n (evalCmd n (st , nats) cmd) cmd₁
evalCmd _ (st , nats) (ℓ := exp) = ({!!} {- st [ ℓ ]← (evalExp st exp)-}) , (evalExp st exp :: nats )
evalCmd _ (st , nats) SKIP = st , nats
evalCmd zero (st , nats) FOR _ := _ TO _ DO _ DONE = st , nats
evalCmd (suc n) (st , nats) FOR x := a TO b DO cmd DONE =
          if evalBExp st (a < b)
            then evalCmd n (st , nats) cmd
          else (st , nats) -- Se dejansko naj izpise *stevec*?? 

-- Pozor: tip funkcije ima smisel zgolj za osnovni tip rezultata
--vsotaPrvihN : Nat → Nat
--vsotaPrvihN n = (evalCmd 125 ( 0 :: (0 :: (0 :: []))) (vsota n)) [ 0 / 2 ]
-}
