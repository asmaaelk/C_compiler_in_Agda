module main where

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

process-file : file → output-type C-file
process-file (File fs) = c-output []

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

