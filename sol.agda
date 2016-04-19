module sol where

import parse
open import lib
open import liskell-types
import liskell

module parsem = parse liskell.gratr2-nt ptr
open parsem
open parsem.parse liskell.rrs liskell.liskell-rtn
open import run ptr

open import c-code

data output-type (T : Set) : Set where
  error-output : string → output-type T -- error message if there is an error
  c-output : T → output-type T -- C source code

{- this function helps us use output-type T as a monad: if the first argument 
   is an error-output, the second will be ignored; otherwise, if the first 
   argument is a c-output, the argument to that c-output constructor will
   be passed as an input to the second argument.  This lets you string together
   output-type values without having to check for error-output every time. -}
_≫=ot_ : ∀{T T' : Set} → output-type T → (T → output-type T') → output-type T'
(error-output e) ≫=ot _ = error-output e
(c-output c) ≫=ot f = f c

-- convert to a var that is not in the namespace of Liskell programs
lvar : string → string
lvar x with x =string "main" 
lvar x | tt = "_main"
lvar x | ff = x

get-head-eq : eq → string
get-head-eq (Eq h p _) = lvar h

get-first-eq : eqs → eq
get-first-eq (EqsCons e _) = e
get-first-eq (EqsStart e) = e

pats-to-list : pats → 𝕃 pat
pats-to-list PatsNil = []
pats-to-list (PatsCons p ps) = p :: pats-to-list ps

get-input-vars : eq → 𝕃 string
get-input-vars (Eq f ps r) with length (pats-to-list ps)
get-input-vars (Eq f ps r) | 0 = []
get-input-vars (Eq f ps r) | suc x = map (λ x → lvar ("x" ^ ℕ-to-string x)) (nats-down x)

err-str1 : string → string → string
err-str1 h h' = "A single block has equations for both " ^ h ^ " and " ^ h' ^ "."

-- return nothing if the heads match, otherwise an error message
check-heads-h : string → eqs → maybe string
check-heads-h h (EqsStart e) = let h' = get-head-eq e in
                                 if h' =string h then nothing else just (err-str1 h h')
check-heads-h h (EqsCons e es) = let h' = get-head-eq e in 
                                   if h' =string h then check-heads-h h es else just (err-str1 h h')

check-heads : eqs → maybe string
check-heads (EqsStart e) = nothing
check-heads (EqsCons e es) = check-heads-h (get-head-eq e) es

lterm-to-term : lterm → term
lterm-to-term (LApp x y) = App (lterm-to-term x) (lterm-to-term y)
lterm-to-term (LPair x y) = Pair (lterm-to-term x) (lterm-to-term y)
lterm-to-term (LStrApp x y) = StrApp (lterm-to-term x) (lterm-to-term y)
lterm-to-term (LId x) = Id x
lterm-to-term (LStrlit x) = Strlit x
lterm-to-term (LParens x) = Parens (lterm-to-term x)

translate-term : term → output-type C-expr
translate-app : term → term → output-type (string × 𝕃 C-expr)
translate-term (Id x) = c-output (Cvar (lvar x))
translate-term (App x y) = translate-app x y ≫=ot λ p → c-output (Ccall (fst p) (reverse (snd p)))
translate-term (Pair x y) = translate-term x ≫=ot λ a → translate-term y ≫=ot λ b → c-output (Ccall "newpair" (a :: b :: []))
translate-term (Parens x) = translate-term x
translate-term (Strlit x) = c-output (Ccall "newstr" [ Cvar x ])
translate-term (StrApp x y) = error-output "String append not supported currently"
translate-app (App x1 x2) y =
  translate-term y ≫=ot (λ a → translate-app x1 x2 ≫=ot (λ p → c-output (fst p , a :: snd p)))
translate-app (Id x) y = translate-term y ≫=ot λ a → c-output (x , [ a ])
translate-app (Parens x) y = translate-app x y
translate-app _ y = error-output "An application is headed by a pair, a string append, or a string literal."

is-callh : term → maybe (string × 𝕃 term)
is-callh (Id x) = just (x , [])
is-callh (App x y) with is-callh x
is-callh (App x y) | just (f , args) = just (f , y :: args)
is-callh (App x y) | nothing = nothing
is-callh (Parens x) = is-callh x
is-callh _ = nothing

-- try to decompose the given term as a function call
is-call : term → maybe (string × 𝕃 term)
is-call t with is-callh t
is-call t | just (f , args) = just (f , reverse args)
is-call t | nothing = nothing

funLabel : string → string
funLabel f = "_start_" ^ f

translate-tail-call : string {- function name -} → 𝕃 string {- input vars -} → 𝕃 term {- args -} → output-type (∀{g : ctxt} → C-code g)
translate-tail-call f [] [] = c-output (Cgoto (funLabel (lvar f)))
translate-tail-call f (v :: vs) (arg :: args) =
  translate-tail-call f vs args ≫=ot λ c →
  translate-term arg ≫=ot λ a → c-output (λ{g : ctxt} → Cseq (Cassign v a ff) (c{g}))
translate-tail-call f _ _ = error-output ("Function " ^ f ^ " is making a tail call with the wrong number of arguments.")

translate-rhs-term : string {- name of function being called -} → 𝕃 string {- input vars -} → term → output-type (∀{g : ctxt} → C-code g)
translate-rhs-term f vs t with is-call t 
translate-rhs-term f vs t | nothing = translate-term t ≫=ot λ a → c-output (λ{g : ctxt} → Creturn{g} a)
translate-rhs-term f vs t | just (f' , args) with f =string f'
translate-rhs-term f vs t | just (f' , args) | ff = translate-term t ≫=ot λ a → c-output (λ{g : ctxt} → Creturn{g} a)
translate-rhs-term f vs t | just (f' , args) | tt = translate-tail-call f vs args

translate-rhs : string {- name of function being called -} → 𝕃 string {- input vars -} → rhs → output-type (∀{g : ctxt} → C-code g)
translate-rhs f vs (RhsTerm t) = translate-rhs-term f vs t
translate-rhs f vs (RhsLterm t) = translate-rhs-term f vs (lterm-to-term t)

ifIsPair : ∀{A : Set} → string × pat → (string → A) → A → A
ifIsPair (x , PatPair _ _) f d = f x
ifIsPair (x , _) f d = d

{-
translate-pats-t (ins : 𝕃 (string × pat)) : Set where
  mk-translate-pats-t : (g : ctxt) → (list-all 
                                       (λ (p : string × pat) → 
                                          ifIsPair (λ x → containsIsPair g x) tt p)
                                       ins) ≡ tt → 
                        translate-pats-t

translate-pats : (ins : 𝕃 (string × pat)) → translate-pats-t ins
-}

translate-eq-only-id-pats : ∀{g : ctxt} → 𝕃 string {- orig input vars -} → 𝕃 string {- input vars -} → eq → 
                            ((∀{g' : ctxt} → C-code g') → C-code g) → 
                            output-type (C-code g)
translate-eq-only-id-pats origvs (x :: xs) (Eq f (PatsCons (PatId y) ps) e) F = 
  translate-eq-only-id-pats origvs xs (Eq f ps e) F ≫=ot λ hs → c-output (Cseq (Cassign y (Cvar x) tt) hs)
translate-eq-only-id-pats origvs [] (Eq f PatsNil e) F = translate-rhs f origvs e ≫=ot λ a → c-output (F a)
translate-eq-only-id-pats _ _ (Eq f _ e) F =
  error-output ("When compiling an equation for " ^ f ^ ", we encountered either a different number of\n" 
              ^ "patterns in two equations, or else a non-variable pattern after the first pattern position.\n")

translate-eq : 𝕃 string {- input vars -} → eq → C-code Cnone → output-type (C-code Cnone)
translate-eq (x :: xs) (Eq f (PatsCons (PatPair p1 p2) ps) e) r = 
 translate-eq-only-id-pats (x :: xs) xs (Eq f ps e)
    (λ h → Cif (Catom (CisPair x))
             (Cseq (CdecomposePair x p1 p2 (||-intro1 (=string-refl x)))
                h)
             r)
translate-eq (x :: xs) (Eq f (PatsCons (PatId y) ps) e) r =
  translate-eq-only-id-pats (x :: xs) xs (Eq f ps e) (λ h → Cseq (Cassign y (Cvar x) tt) h)
translate-eq (x :: xs) (Eq f (PatsCons (PatStrlit y) ps) e) r = 
  translate-eq-only-id-pats (x :: xs) xs (Eq f ps e) (λ h → (Cif (Catom (CisStr x y)) h r))
translate-eq [] (Eq f PatsNil e) r = translate-rhs f [] e ≫=ot λ h → c-output h
translate-eq _ (Eq f _ e) r = 
  error-output ("Two equations for " ^ f ^ " have different numbers of patterns.")

translate-bodies : 𝕃 string {- input vars -} → eqs → output-type (C-code Cnone)
translate-bodies vs (EqsStart e) = translate-eq vs e (Creturn (Ccall "labort" []))
translate-bodies vs (EqsCons e es) = translate-bodies vs es ≫=ot (λ bs → translate-eq vs e bs)

process-fundef : fundef → output-type C-fun
process-fundef (Fundef _ es) with check-heads es
process-fundef (Fundef _ es) | nothing = 
  let e = get-first-eq es in
  let inputs = get-input-vars e in
  let f = get-head-eq e in
    translate-bodies inputs es ≫=ot λ c → c-output (Cfun f inputs (Clabel (funLabel f) c))
process-fundef (Fundef _ es) | just m = error-output m

process-fundefs : fundefs → output-type C-file
process-fundefs (FundefsCons f fs) = process-fundef f ≫=ot λ d → process-fundefs fs ≫=ot λ ds → c-output (d :: ds)
process-fundefs (FundefsStart f) = process-fundef f ≫=ot λ d → c-output [ d ]

process-file : file → output-type C-file
process-file (File fs) = 
  process-fundefs fs ≫=ot
    (λ cs → 
       let vs = "argc" :: "argv" :: [] in
         c-output (cs ++ [ Cfun "main" vs
                            (Creturn (Ccall "print" [ (Ccall "_main" [ (Ccall "convert" (map Cvar vs)) ]) ] )) ] ))

process : {lc : 𝕃 char} → Run lc → output-type C-file
process (ParseTree{s = "file"}{parsed-file p} ipt ::' []') = process-file p
process r = error-output ("Parsing failure (run with -" ^ "-showParsed).\n")

putStrRunIf : {lc : 𝕃 char} → 𝔹 → Run lc → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

doOutput : output-type C-file → string → IO ⊤
doOutput (error-output s) basename = putStr ("Error: " ^ s ^ "\n")
doOutput (c-output c) basename = 
  writeFile (basename ^ ".c") (C-file-to-string c)

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed (input-filename :: []) = (readFiniteFile input-filename) >>= processText
  where processText : string → IO ⊤
        processText x with runRtn (string-to-𝕃char x)
        processText x | s with s
        processText x | s | inj₁ cs = putStr "Characters left before failure : " >>
                                        putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> doOutput (process r') (base-filename input-filename)
                                     
processArgs showRun showParsed ("--showRun" :: xs) = processArgs tt showParsed xs 
processArgs showRun showParsed ("--showParsed" :: xs) = processArgs showRun tt xs 
processArgs showRun showParsed (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff

