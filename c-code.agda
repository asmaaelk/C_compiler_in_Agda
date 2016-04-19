module c-code where

open import lib

data C-atom : Set where
  CisPair : string → C-atom
  CisStr : string → string → C-atom

data C-guard : Set where
  Catom : C-atom → C-guard
  Cand : C-guard → C-guard → C-guard
  Cnone : C-guard

ctxt : Set
ctxt = C-guard

containsIsPair : ctxt → string → 𝔹
containsIsPair (Cand c1 c2) s = containsIsPair c1 s || containsIsPair c2 s
containsIsPair (Catom (CisPair s')) s = s' =string s
containsIsPair (Catom (CisStr _ _)) _ = ff
containsIsPair Cnone _ = ff

data C-expr : Set where
  CnewPair : C-expr → C-expr → C-expr
  CnewStr : C-expr → C-expr
  Ccall : string → 𝕃 C-expr → C-expr
  Cvar : string → C-expr

data C-code : ctxt → Set where
  Cseq : {g : ctxt} → C-code g → C-code g → C-code g
  Cif : {g : ctxt} → (e : C-guard) → C-code (Cand e g) → C-code g → C-code g
  CdecomposePair : {g : ctxt} (x : string)(p1 p2 : string) → containsIsPair g x ≡ tt → C-code g
  Cassign : {g : ctxt} (x : string)(y : C-expr)(declare-x : 𝔹) → C-code g
  Creturn : {g : ctxt} → C-expr → C-code g 
  Clabel : {g : ctxt} → string → C-code g → C-code g
  Cgoto : {g : ctxt} → string → C-code g 
  
data C-fun : Set where
  {- Cfun f inputs code:
     -- f is the name of the function
     -- inputs is a list of the input variables for the function
     -- code is the body
   -}
  Cfun : string → 𝕃 string → C-code Cnone → C-fun

C-file : Set
C-file = 𝕃 C-fun

C-check-tag : string → string → string
C-check-tag x t = "(*(int *)" ^ x ^ " == " ^ t ^ ")"

C-atom-to-string : C-atom → string
C-atom-to-string (CisPair x) = C-check-tag x "PAIR"
C-atom-to-string (CisStr x y) = C-check-tag x "STR" ^ " && strcmp(&((char *) " ^ x ^ ")[4], " ^ y ^ ") == 0"

C-guard-to-string : C-guard → string
C-guard-to-string (Cand c1 c2) = C-guard-to-string c1 ^ " && " ^ C-guard-to-string c2
C-guard-to-string (Catom a) = C-atom-to-string a
C-guard-to-string Cnone = "1" -- for true

C-expr-to-string : C-expr → string
C-exprs-to-strings : 𝕃 C-expr → 𝕃 string
C-expr-to-string (CnewPair e1 e2) = "newpair(" ^ C-expr-to-string e1 ^ " , " ^ C-expr-to-string e2 ^ ")"
C-expr-to-string (CnewStr e1) = "newstr(" ^ C-expr-to-string e1 ^ ")"
C-expr-to-string (Ccall f args) = f ^ "(" ^ (string-concat-sep " , " (C-exprs-to-strings args)) ^ ")"
C-expr-to-string (Cvar x) = x
C-exprs-to-strings [] = []
C-exprs-to-strings (e :: es) = C-expr-to-string e :: C-exprs-to-strings es

C-code-to-string : ∀{g : ctxt} → C-code g → string
C-code-to-string (Cseq c1 c2) = (C-code-to-string c1) ^ (C-code-to-string c2)
C-code-to-string (Cif e c1 c2) = "if (" ^ C-guard-to-string e ^ ") {\n" ^ C-code-to-string c1 ^ "} else {\n" ^ C-code-to-string c2 ^ "}\n"
C-code-to-string (Cassign x y declare) = (if declare then "void *" else "") ^ x ^ " = " ^ (C-expr-to-string y) ^ ";\n"
C-code-to-string (CdecomposePair x p1 p2 _) =
  "void *" ^ p1 ^ " =  ((pair *)" ^ x ^ ")->p1;\nvoid *" ^ p2 ^ " = ((pair *)" ^ x ^ ")->p2;\n"
C-code-to-string (Creturn e) = "return " ^ (C-expr-to-string e) ^ ";\n"
C-code-to-string (Clabel l c) = l ^ ": {" ^ C-code-to-string c ^ "}\n"
C-code-to-string (Cgoto l) = "goto " ^ l ^ ";\n"

c-start : string
c-start = 
 "#include <stdio.h>\n" ^
 "#include <stdlib.h>\n" ^
 "#include <string.h>\n\n" ^
 "typedef struct {\n" ^
 "  int tag;\n" ^
 "  void *p1;\n" ^
 "  void *p2;\n" ^
 "} pair;\n" ^
 "\n" ^
 "typedef struct {\n" ^
 "  int tag;\n" ^
 "  char cs;\n" ^
 "} str;\n" ^
 "\n" ^
 "#define PAIR 0\n" ^
 "#define STR 1\n\n" ^
 "pair *newpair(void *p1, void *p2) {\n" ^
 "  pair *p = (pair *)malloc(sizeof(pair));\n" ^
 "  p->tag = PAIR;\n" ^
 "  p->p1 = p1;\n" ^
 "  p->p2 = p2;\n" ^
 "  return p;\n" ^
 "}\n" ^
 "\n" ^
 "str *newstr(char *cs) {\n" ^
 "  int len = strlen(cs);\n" ^
 "  int sz = sizeof(int) + (4*(len+1))/4;\n" ^
 "  str *s = (str *)malloc(sz);\n" ^
 "  s->tag = STR;\n" ^
 "  strcpy(&s->cs,cs);\n" ^
 "  return s;\n" ^
 "}\n\n" ^
 "void printh(void *x) {\n" ^
 "  if (*((int *)x) == PAIR) {\n" ^
 "    // it is a pair\n" ^
 "    pair *p = (pair *)x;\n" ^
 "    printf(\"[\");\n" ^
 "    printh(p->p1);\n" ^
 "    printf(\",\");\n" ^
 "    printh(p->p2);\n" ^
 "    printf(\"]\");\n" ^
 "  }\n" ^
 "  else {\n" ^
 "    // it is a string\n" ^
 "    str *s = (str *)x;\n" ^
 "    printf(\"\\\"\");\n" ^
 "    fputs(&s->cs, stdout);\n" ^
 "    printf(\"\\\"\");\n" ^
 "  }\n" ^
 "}\n\n" ^
 "int print(void *x) {\n" ^ 
 "  printh(x);\n" ^
 "  printf(\"\\n\");\n" ^
 "  return 0;\n" ^
 "}\n\n" ^
 "void *convert(int argc, char **argv) {\n" ^
 "  int i;\n" ^
 "  void **r = (void **)0;\n" ^
 "  for (i = argc - 1; i > 0; i--) {\n" ^
 "    if (!r) \n" ^
 "      r = newstr(argv[i]);\n" ^
 "    else\n" ^
 "      r = newpair(newstr(argv[i]),r);\n" ^
 "  }\n" ^
 "  if (!r)\n" ^
 "    r = newstr(\"\");\n" ^
 "  return r;\n" ^
 "}\n\n" ^
 "int labort() {\n" ^
 "  exit(1);\n" ^
 "  return 0;\n" ^
 "}\n\n"


C-fun-to-string : C-fun → string
C-fun-to-string (Cfun f inputs body) = 
  "void *" ^ f ^ "(" ^ string-concat-sep "," (map (λ s → "void *" ^ s) inputs) ^ ") {\n" ^ C-code-to-string body ^ "}\n"

C-file-to-string : C-file → string 
C-file-to-string l = c-start ^ string-concat (map C-fun-to-string l)
  